-- Prove2me | solution 1 for CookSensitivity.ChvatalRank.chvatalIter_eq_empty_of_no_integer_point
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:01:25.920186+00:00
-- url     : https://prove2.me/submissions/ed502105-a55b-4878-8333-185a85907b38

import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
import Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure
import Theorems.Thm_CookSensitivity_ChvatalRank_exists_flat_direction_of_no_integer_point

open CookSensitivity.ChvatalRank
open Matrix
open scoped Classical

/-! ### Section 1: Fourier-Motzkin Elimination and Farkas' Lemma over `ℚ` -/

private lemma fm_between {ι : Type*} [Fintype ι] (α l u : ι → ℚ)
    (h : ∀ p q, 0 < α p → α q < 0 → l q ≤ u p) :
    ∃ t : ℚ, (∀ q, α q < 0 → l q ≤ t) ∧ ∀ p, 0 < α p → t ≤ u p := by
  by_cases hN : (Finset.univ.filter (fun q => α q < 0)).Nonempty
  · obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image _ l hN
    refine ⟨l q0, fun q hq => hmax q (by simpa using hq),
      fun p hp => h p q0 hp (by simpa using hq0)⟩
  · by_cases hP : (Finset.univ.filter (fun p => 0 < α p)).Nonempty
    · obtain ⟨p0, hp0, hmin⟩ := Finset.exists_min_image _ u hP
      refine ⟨u p0, fun q hq => ?_, fun p hp => hmin p (by simpa using hp)⟩
      exact absurd ⟨q, by simpa using hq⟩ hN
    · refine ⟨0, fun q hq => ?_, fun p hp => ?_⟩
      · exact absurd ⟨q, by simpa using hq⟩ hN
      · exact absurd ⟨p, by simpa using hp⟩ hP

private theorem farkas_fm : ∀ (n : ℕ) {ι : Type*} [Fintype ι] (a : ι → Fin n → ℚ) (b : ι → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, a i ⬝ᵥ x ≤ b i) →
    ∃ μ : ι → ℚ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • a i = 0) ∧ ∑ i, μ i * b i < 0 := by
  intro n
  induction n with
  | zero =>
    intro ι _ a b h
    have : ∃ i, b i < 0 := by
      by_contra hc
      push_neg at hc
      exact h ⟨0, fun i => by simpa using hc i⟩
    obtain ⟨i0, hi0⟩ := this
    refine ⟨fun i => if i = i0 then 1 else 0,
      fun i => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
    · funext j; exact j.elim0
    · simpa using hi0
  | succ n ih =>
    intro ι _ a b h
    set α : ι → ℚ := fun i => a i 0 with hα
    set a' : ι → Fin n → ℚ := fun i j => a i j.succ with ha'
    have hdot : ∀ i (t : ℚ) (x' : Fin n → ℚ),
        a i ⬝ᵥ (vecCons t x') = α i * t + a' i ⬝ᵥ x' := by
      intro i t x'
      simp only [dotProduct, Fin.sum_univ_succ, hα, ha']
      simp
    let W : ι × ι → ι → ℚ := fun pq l =>
      (if α pq.1 = 0 ∧ pq.1 = pq.2 ∧ l = pq.1 then 1 else 0) +
      (if 0 < α pq.1 ∧ α pq.2 < 0 then
        ((if l = pq.1 then -α pq.2 else 0) + (if l = pq.2 then α pq.1 else 0)) else 0)
    have hW0 : ∀ pq l, 0 ≤ W pq l := by
      intro pq l
      simp only [W]
      split_ifs <;> first | linarith | (try norm_num) <;> nlinarith
    have hW1 : ∀ i, α i = 0 → ∀ v : ι → ℚ, ∑ l, W (i, i) l * v l = v i := by
      intro i hi v
      have : ∀ l, W (i, i) l = if l = i then 1 else 0 := by
        intro l; simp [W, hi]
      simp [this]
    have hW2 : ∀ p q, 0 < α p → α q < 0 → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = -α q * v p + α p * v q := by
      intro p q hp hq v
      have hpq : p ≠ q := fun e => by subst e; linarith
      have : ∀ l, W (p, q) l = (if l = p then -α q else 0) + (if l = q then α p else 0) := by
        intro l; simp [W, hp, hq, hp.ne', hpq]
      simp [this, add_mul, Finset.sum_add_distrib]
    have hW3 : ∀ p q, ¬ (α p = 0 ∧ p = q) → ¬ (0 < α p ∧ α q < 0) → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = 0 := by
      intro p q h1 h2 v
      have : ∀ l, W (p, q) l = 0 := by
        intro l
        have h1' : ¬ (α p = 0 ∧ p = q ∧ l = p) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [W]; rw [if_neg h1', if_neg h2]; simp
      simp [this]
    have hWα : ∀ pq, ∑ l, W pq l * α l = 0 := by
      intro pq
      obtain ⟨p, q⟩ := pq
      by_cases h1 : α p = 0 ∧ p = q
      · obtain ⟨h1a, rfl⟩ := h1
        rw [hW1 p h1a]; exact h1a
      · by_cases h2 : 0 < α p ∧ α q < 0
        · rw [hW2 p q h2.1 h2.2]; ring
        · exact hW3 p q h1 h2 _
    let a'' : ι × ι → Fin n → ℚ := fun pq => ∑ l, W pq l • a' l
    let b'' : ι × ι → ℚ := fun pq => ∑ l, W pq l * b l
    have hinf : ¬ ∃ x' : Fin n → ℚ, ∀ pq, a'' pq ⬝ᵥ x' ≤ b'' pq := by
      rintro ⟨x', hx'⟩
      have hex := fm_between α (fun q => (b q - a' q ⬝ᵥ x') / α q)
        (fun p => (b p - a' p ⬝ᵥ x') / α p) (by
          intro p q hp hq
          have := hx' (p, q)
          have e1 : a'' (p, q) ⬝ᵥ x' = ∑ l, W (p, q) l * (a' l ⬝ᵥ x') := by
            simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [e1] at this
          have hsum : ∑ l, W (p, q) l * (a' l ⬝ᵥ x') = -α q * (a' p ⬝ᵥ x') + α p * (a' q ⬝ᵥ x') :=
            hW2 p q hp hq _
          have hb : b'' (p, q) = -α q * b p + α p * b q := hW2 p q hp hq _
          rw [hsum, hb] at this
          rw [div_le_iff_of_neg hq, div_mul_eq_mul_div, div_le_iff₀ hp]
          nlinarith)
      obtain ⟨t, htl, htu⟩ := hex
      apply h
      refine ⟨vecCons t x', fun i => ?_⟩
      rw [hdot]
      rcases lt_trichotomy (α i) 0 with hi | hi | hi
      · have := htl i hi
        rw [div_le_iff_of_neg hi] at this
        linarith
      · have := hx' (i, i)
        have e1 : a'' (i, i) ⬝ᵥ x' = a' i ⬝ᵥ x' := by
          simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          exact hW1 i hi (fun l => a' l ⬝ᵥ x')
        have e2 : b'' (i, i) = b i := hW1 i hi b
        rw [e1, e2] at this
        rw [hi]; linarith
      · have := htu i hi
        rw [le_div_iff₀ hi] at this
        linarith
    obtain ⟨μ'', hμ0, hμa, hμb⟩ := ih a'' b'' hinf
    refine ⟨fun l => ∑ pq, μ'' pq * W pq l,
      fun l => Finset.sum_nonneg (fun pq _ => mul_nonneg (hμ0 pq) (hW0 pq l)), ?_, ?_⟩
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have : ∀ l, a l 0 = α l := fun l => rfl
        simp only [this]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * α l
            = ∑ pq, μ'' pq * ∑ l, W pq l * α l := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by simp [hWα]
      · have := congrFun hμa j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, a''] at this ⊢
        have e : ∀ l, a l j.succ = a' l j := fun l => rfl
        simp only [e]
        calc ∑ l, (∑ pq, μ'' pq * W pq l) * a' l j
            = ∑ pq, μ'' pq * ∑ l, W pq l * a' l j := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          _ = 0 := by rw [← this]
    · calc ∑ l, (∑ pq, μ'' pq * W pq l) * b l
          = ∑ pq, μ'' pq * b'' pq := by
            simp only [b'', Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ < 0 := hμb

private lemma farkas_dual {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℚ) (g : ι → ℚ) (c : Fin n → ℚ)
    (k : ℚ) (x0 : Fin n → ℚ) (hx0 : ∀ i, a i ⬝ᵥ x0 ≤ g i)
    (hlt : ∀ x : Fin n → ℚ, (∀ i, a i ⬝ᵥ x ≤ g i) → c ⬝ᵥ x < k) :
    ∃ y : ι → ℚ, (∀ i, 0 ≤ y i) ∧ ∑ i, y i • a i = c ∧ ∑ i, y i * g i < k := by
  let a2 : Option ι → Fin n → ℚ := fun o => match o with
    | none => -c
    | some i => a i
  let b2 : Option ι → ℚ := fun o => match o with
    | none => -k
    | some i => g i
  have hinf : ¬ ∃ x : Fin n → ℚ, ∀ o, a2 o ⬝ᵥ x ≤ b2 o := by
    rintro ⟨x, hx⟩
    have h1 : ∀ i, a i ⬝ᵥ x ≤ g i := fun i => hx (some i)
    have h2 : -c ⬝ᵥ x ≤ -k := hx none
    have := hlt x h1
    rw [neg_dotProduct] at h2
    linarith
  obtain ⟨μ, hμ0, hμa, hμb⟩ := farkas_fm n a2 b2 hinf
  rw [Fintype.sum_option] at hμa hμb
  simp only [a2, b2] at hμa hμb
  have hlam := hμ0 none
  have hsum : ∑ i, μ (some i) * (a i ⬝ᵥ x0) ≤ ∑ i, μ (some i) * g i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx0 i) (hμ0 _)
  have hdot : ∑ i, μ (some i) * (a i ⬝ᵥ x0) = (∑ i, μ (some i) • a i) ⬝ᵥ x0 := by
    rw [sum_dotProduct]; simp [smul_dotProduct]
  rcases hlam.lt_or_eq with hpos | hzero
  · refine ⟨fun i => μ (some i) / μ none, fun i => div_nonneg (hμ0 _) hpos.le, ?_, ?_⟩
    · have : ∑ i, μ (some i) • a i = μ none • c := by
        have : ∑ i, μ (some i) • a i + μ none • -c = 0 := by rw [add_comm]; exact hμa
        rw [smul_neg] at this
        exact sub_eq_zero.1 (by rw [sub_eq_add_neg]; exact this)
      calc ∑ i, (μ (some i) / μ none) • a i = (μ none)⁻¹ • ∑ i, μ (some i) • a i := by
            rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [smul_smul, div_eq_inv_mul]
        _ = c := by rw [this, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    · have : ∑ i, μ (some i) * g i + μ none * -k < 0 := by rw [add_comm]; exact hμb
      have h3 : ∑ i, μ (some i) * g i < μ none * k := by linarith
      calc ∑ i, μ (some i) / μ none * g i = (∑ i, μ (some i) * g i) / μ none := by
            rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
        _ < k := by rw [div_lt_iff₀ hpos]; linarith
  · exfalso
    rw [← hzero] at hμa hμb
    simp at hμa hμb
    rw [hμa, zero_dotProduct] at hdot
    linarith

/-- Fourier-Motzkin projection of `n` variables onto a single parameter `t : ℚ`. -/
private theorem fm_proj : ∀ (n : ℕ) {ι : Type} [Fintype ι]
    (γ : ι → ℚ) (a : ι → Fin n → ℚ) (b : ι → ℚ),
    ∃ (κ : Type) (_ : Fintype κ) (γ' : κ → ℚ) (b' : κ → ℚ),
      ∀ t : ℚ, (∃ x : Fin n → ℚ, ∀ i, γ i * t + a i ⬝ᵥ x ≤ b i) ↔
        (∀ j : κ, γ' j * t ≤ b' j) := by
  intro n
  induction n with
  | zero =>
    intro ι _ γ a b
    refine ⟨ι, inferInstance, γ, b, fun t => ?_⟩
    constructor
    · rintro ⟨x, hx⟩ i
      simpa using hx i
    · intro h
      exact ⟨0, fun i => by simpa using h i⟩
  | succ n ih =>
    intro ι _ γ a b
    set α : ι → ℚ := fun i => a i 0 with hα
    set a' : ι → Fin n → ℚ := fun i j => a i j.succ with ha'
    have hdot : ∀ i (s : ℚ) (x' : Fin n → ℚ),
        a i ⬝ᵥ (vecCons s x') = α i * s + a' i ⬝ᵥ x' := by
      intro i s x'
      simp only [dotProduct, Fin.sum_univ_succ, hα, ha']
      simp
    let W : ι × ι → ι → ℚ := fun pq l =>
      (if α pq.1 = 0 ∧ pq.1 = pq.2 ∧ l = pq.1 then 1 else 0) +
      (if 0 < α pq.1 ∧ α pq.2 < 0 then
        ((if l = pq.1 then -α pq.2 else 0) + (if l = pq.2 then α pq.1 else 0)) else 0)
    have hW0 : ∀ pq l, 0 ≤ W pq l := by
      intro pq l
      simp only [W]
      split_ifs <;> first | linarith | (try norm_num) <;> nlinarith
    have hW1 : ∀ i, α i = 0 → ∀ v : ι → ℚ, ∑ l, W (i, i) l * v l = v i := by
      intro i hi v
      have : ∀ l, W (i, i) l = if l = i then 1 else 0 := by
        intro l; simp [W, hi]
      simp [this]
    have hW2 : ∀ p q, 0 < α p → α q < 0 → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = -α q * v p + α p * v q := by
      intro p q hp hq v
      have hpq : p ≠ q := fun e => by subst e; linarith
      have : ∀ l, W (p, q) l = (if l = p then -α q else 0) + (if l = q then α p else 0) := by
        intro l; simp [W, hp, hq, hp.ne', hpq]
      simp [this, add_mul, Finset.sum_add_distrib]
    have hW3 : ∀ p q, ¬ (α p = 0 ∧ p = q) → ¬ (0 < α p ∧ α q < 0) → ∀ v : ι → ℚ,
        ∑ l, W (p, q) l * v l = 0 := by
      intro p q h1 h2 v
      have : ∀ l, W (p, q) l = 0 := by
        intro l
        have h1' : ¬ (α p = 0 ∧ p = q ∧ l = p) := fun h => h1 ⟨h.1, h.2.1⟩
        simp only [W]; rw [if_neg h1', if_neg h2]; simp
      simp [this]
    have hWα : ∀ pq, ∑ l, W pq l * α l = 0 := by
      intro pq
      obtain ⟨p, q⟩ := pq
      by_cases h1 : α p = 0 ∧ p = q
      · obtain ⟨h1a, rfl⟩ := h1
        rw [hW1 p h1a]; exact h1a
      · by_cases h2 : 0 < α p ∧ α q < 0
        · rw [hW2 p q h2.1 h2.2]; ring
        · exact hW3 p q h1 h2 _
    let γ'' : ι × ι → ℚ := fun pq => ∑ l, W pq l * γ l
    let a'' : ι × ι → Fin n → ℚ := fun pq => ∑ l, W pq l • a' l
    let b'' : ι × ι → ℚ := fun pq => ∑ l, W pq l * b l
    obtain ⟨κ, hκ, γ', b', hih⟩ := ih γ'' a'' b''
    refine ⟨κ, hκ, γ', b', fun t => ?_⟩
    rw [← hih t]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨fun j => x j.succ, fun pq => ?_⟩
      have hlin : γ'' pq * t + a'' pq ⬝ᵥ (fun j => x j.succ) =
          ∑ l, W pq l * (γ l * t + a l ⬝ᵥ x) := by
        have hx_cons : vecCons (x 0) (fun j => x j.succ) = x := by
          ext j; refine Fin.cases rfl (fun _ => rfl) j
        have hdot' : ∀ l, a l ⬝ᵥ x = α l * x 0 + a' l ⬝ᵥ (fun j => x j.succ) := by
          intro l
          conv_lhs => rw [← hx_cons]
          exact hdot l (x 0) (fun j => x j.succ)
        simp only [γ'', a'', sum_dotProduct, smul_dotProduct, smul_eq_mul, hdot']
        calc
          (∑ l, W pq l * γ l) * t + ∑ l, W pq l * (a' l ⬝ᵥ fun j => x j.succ)
            = (∑ l, W pq l * γ l) * t + (∑ l, W pq l * α l) * x 0 +
                ∑ l, W pq l * (a' l ⬝ᵥ fun j => x j.succ) := by
              rw [hWα pq, zero_mul, add_zero]
          _ = ∑ l, W pq l * (γ l * t + (α l * x 0 + a' l ⬝ᵥ fun j => x j.succ)) := by
              simp only [Finset.sum_mul, mul_add, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun l _ => by ring
      rw [hlin]
      exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hx l) (hW0 pq l)
    · rintro ⟨x', hx'⟩
      have hex := fm_between α (fun q => (b q - γ q * t - a' q ⬝ᵥ x') / α q)
        (fun p => (b p - γ p * t - a' p ⬝ᵥ x') / α p) (by
          intro p q hp hq
          have := hx' (p, q)
          have e1 : a'' (p, q) ⬝ᵥ x' = ∑ l, W (p, q) l * (a' l ⬝ᵥ x') := by
            simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          rw [e1] at this
          have hsum : ∑ l, W (p, q) l * (a' l ⬝ᵥ x') = -α q * (a' p ⬝ᵥ x') + α p * (a' q ⬝ᵥ x') :=
            hW2 p q hp hq _
          have hb : b'' (p, q) = -α q * b p + α p * b q := hW2 p q hp hq _
          have hγ : γ'' (p, q) = -α q * γ p + α p * γ q := hW2 p q hp hq _
          rw [hsum, hb, hγ] at this
          rw [div_le_iff_of_neg hq, div_mul_eq_mul_div, div_le_iff₀ hp]
          nlinarith)
      obtain ⟨s, hsl, hsu⟩ := hex
      refine ⟨vecCons s x', fun i => ?_⟩
      rw [hdot]
      rcases lt_trichotomy (α i) 0 with hi | hi | hi
      · have := hsl i hi
        rw [div_le_iff_of_neg hi] at this
        linarith
      · have := hx' (i, i)
        have e1 : a'' (i, i) ⬝ᵥ x' = a' i ⬝ᵥ x' := by
          simp only [a'', sum_dotProduct, smul_dotProduct, smul_eq_mul]
          exact hW1 i hi (fun l => a' l ⬝ᵥ x')
        have e2 : b'' (i, i) = b i := hW1 i hi b
        have e3 : γ'' (i, i) = γ i := hW1 i hi γ
        rw [e1, e2, e3] at this
        rw [hi]; linarith
      · have := hsu i hi
        rw [le_div_iff₀ hi] at this
        linarith

/-! ### Section 2: Rational Polyhedra Have Integral Matrix & RHS Descriptions -/

private lemma rat_mul_nat_eq_int (q : ℚ) (M : ℕ) (h : q.den ∣ M) :
    ∃ z : ℤ, (M : ℚ) * q = (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨(c : ℤ) * q.num, ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  calc
    ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * (q.den : ℚ)) := by push_cast; ring
    _ = (c : ℚ) * (q.num : ℚ) := by rw [Rat.mul_den_eq_num]
    _ = (((c : ℤ) * q.num : ℤ) : ℚ) := by push_cast; ring

private lemma isPolyhedron_iff_int_system {n : ℕ} (P : Set (Fin n → ℚ)) :
    IsPolyhedron P ↔
      ∃ (k : ℕ) (A : Matrix (Fin k) (Fin n) ℤ) (b : Fin k → ℤ),
        P = {x | ∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ x ≤ (b i : ℚ)} := by
  constructor
  · rintro ⟨k, D, d, rfl⟩
    let M : Fin k → ℕ := fun i => (d i).den * ∏ j : Fin n, (D i j).den
    have hM_pos : ∀ i, 0 < (M i : ℚ) := by
      intro i
      exact Nat.cast_pos.mpr (Nat.mul_pos (d i).pos (Finset.prod_pos fun j _ => (D i j).pos))
    have hA : ∀ i j, ∃ z : ℤ, (M i : ℚ) * D i j = (z : ℚ) := by
      intro i j
      apply rat_mul_nat_eq_int
      exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) _
    have hb : ∀ i, ∃ z : ℤ, (M i : ℚ) * d i = (z : ℚ) := by
      intro i
      apply rat_mul_nat_eq_int
      exact dvd_mul_right _ _
    choose A hA_eq using hA
    choose b hb_eq using hb
    refine ⟨k, Matrix.of A, b, ?_⟩
    ext x
    simp only [Set.mem_setOf_eq, Pi.le_def, mulVec, dotProduct, Matrix.of_apply]
    refine forall_congr' fun i => ?_
    have hsum : ∑ j : Fin n, (A i j : ℚ) * x j = (M i : ℚ) * ∑ j : Fin n, D i j * x j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hA_eq i j, mul_assoc]
    rw [hsum, ← hb_eq i]
    exact ⟨fun h => mul_le_mul_of_nonneg_left h (hM_pos i).le,
      fun h => le_of_mul_le_mul_left h (hM_pos i)⟩
  · rintro ⟨k, A, b, rfl⟩
    refine ⟨k, A.map (Int.cast : ℤ → ℚ), fun i => (b i : ℚ), ?_⟩
    ext x
    simp [Pi.le_def, mulVec, dotProduct]

/-! ### Section 3: Basic Properties of `IsIntegral` and `chvatalClosure` -/

private lemma int_dot_integral {n : ℕ} (a : Fin n → ℤ) {z : Fin n → ℚ} (hz : IsIntegral z) :
    ∃ k : ℤ, (fun i => (a i : ℚ)) ⬝ᵥ z = (k : ℚ) := by
  choose f hf using hz
  refine ⟨∑ i, a i * f i, ?_⟩
  simp only [dotProduct, hf, Int.cast_sum, Int.cast_mul]

private lemma isIntegral_add {n : ℕ} {x y : Fin n → ℚ} (hx : IsIntegral x) (hy : IsIntegral y) :
    IsIntegral (x + y) := by
  intro i
  obtain ⟨kx, hkx⟩ := hx i
  obtain ⟨ky, hky⟩ := hy i
  exact ⟨kx + ky, by simp [hkx, hky]⟩

private lemma isIntegral_natSmul {n : ℕ} (m : ℕ) {x : Fin n → ℚ} (hx : IsIntegral x) :
    IsIntegral ((m : ℚ) • x) := by
  intro i
  obtain ⟨k, hk⟩ := hx i
  exact ⟨(m : ℤ) * k, by simp [Pi.smul_apply, smul_eq_mul, hk]⟩

private lemma chvatalClosure_mono {n : ℕ} {S T : Set (Fin n → ℚ)} (hST : S ⊆ T) :
    chvatalClosure S ⊆ chvatalClosure T := by
  intro x hx a β hT
  exact hx a β (fun y hy => hT y (hST hy))

private lemma chvatalIter_mono {n : ℕ} (t : ℕ) {S T : Set (Fin n → ℚ)} (hST : S ⊆ T) :
    chvatalIter t S ⊆ chvatalIter t T := by
  induction t with
  | zero => exact hST
  | succ t ih =>
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply]
    exact chvatalClosure_mono ih

private lemma chvatalIter_add {n : ℕ} (t₁ t₂ : ℕ) (S : Set (Fin n → ℚ)) :
    chvatalIter (t₁ + t₂) S = chvatalIter t₁ (chvatalIter t₂ S) := by
  simp only [chvatalIter, Function.iterate_add_apply]

private lemma chvatalClosure_subset_self_of_isPolyhedron {n : ℕ} {P : Set (Fin n → ℚ)}
    (hP : IsPolyhedron P) : chvatalClosure P ⊆ P := by
  obtain ⟨k, A, b, rfl⟩ := (isPolyhedron_iff_int_system P).mp hP
  intro x hx i
  have h := hx (A i) (b i : ℚ) (fun y hy => hy i)
  simpa using h

private lemma chvatalClosure_empty {n : ℕ} :
    chvatalClosure (∅ : Set (Fin n → ℚ)) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have h := hx 0 (-1 : ℚ) (by simp)
  norm_num at h

private lemma floor_half_add_floor_add_one (β : ℚ) :
    ⌊(β + ((⌊β⌋ : ℚ) + 1)) / 2⌋ = ⌊β⌋ ∧ β < (β + ((⌊β⌋ : ℚ) + 1)) / 2 := by
  have h1 : (⌊β⌋ : ℚ) ≤ β := Int.floor_le β
  have h2 : β < (⌊β⌋ : ℚ) + 1 := Int.lt_floor_add_one β
  refine ⟨Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩, by linarith⟩

/-! ### Section 4: Chvátal Closure of a Rational Polyhedron is a Rational Polyhedron -/

private theorem isPolyhedron_chvatalClosure {n : ℕ} {P : Set (Fin n → ℚ)}
    (hP : IsPolyhedron P) : IsPolyhedron (chvatalClosure P) := by
  by_cases hPemp : P = ∅
  · subst hPemp
    rw [chvatalClosure_empty]
    refine ⟨1, 0, fun _ => -1, ?_⟩
    ext x
    simp [Pi.le_def]
  · obtain ⟨x0, hx0P⟩ := Set.nonempty_iff_ne_empty.mpr hPemp
    obtain ⟨k, A, b, hP_eq⟩ := (isPolyhedron_iff_int_system P).mp hP
    let R : Fin n → ℤ := fun j => ∑ i : Fin k, |A i j|
    let Box : Set (Fin n → ℤ) := {c | ∀ j, |c j| ≤ R j}
    have hBox_fin : Box.Finite := by
      have hIcc : (Set.Icc (-R) R : Set (Fin n → ℤ)).Finite := Set.finite_Icc (-R) R
      refine hIcc.subset ?_
      intro c hc
      exact ⟨fun j => (abs_le.mp (hc j)).1, fun j => (abs_le.mp (hc j)).2⟩
    let B : Set (Fin n → ℤ) :=
      {c ∈ Box | ∃ β : ℚ, ∀ y ∈ P, (fun j => (c j : ℚ)) ⬝ᵥ y ≤ β}
    have hB_fin : B.Finite := hBox_fin.subset (fun c hc => hc.1)
    letI : Fintype B := hB_fin.fintype
    have hex_m : ∀ c : B, ∃ m : ℕ, ∃ β : ℚ,
        (∀ y ∈ P, (fun j => (c.1 j : ℚ)) ⬝ᵥ y ≤ β) ∧
        ⌊β⌋ = ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋ + (m : ℤ) := by
      intro c
      obtain ⟨β, hβ⟩ := c.2.2
      have hle : ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋ ≤ ⌊β⌋ :=
        Int.floor_mono (hβ x0 hx0P)
      refine ⟨(⌊β⌋ - ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋).toNat, β, hβ, ?_⟩
      omega
    let m_c : B → ℤ := fun c =>
      ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋ + (Nat.find (hex_m c) : ℤ)
    have hm_c_spec : ∀ c : B, ∃ β : ℚ,
        (∀ y ∈ P, (fun j => (c.1 j : ℚ)) ⬝ᵥ y ≤ β) ∧ ⌊β⌋ = m_c c :=
      fun c => Nat.find_spec (hex_m c)
    have hm_c_le : ∀ (c : B) (β : ℚ),
        (∀ y ∈ P, (fun j => (c.1 j : ℚ)) ⬝ᵥ y ≤ β) → m_c c ≤ ⌊β⌋ := by
      intro c β hβ
      have hle : ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋ ≤ ⌊β⌋ :=
        Int.floor_mono (hβ x0 hx0P)
      have hnot : ¬ (⌊β⌋ - ⌊(fun j => (c.1 j : ℚ)) ⬝ᵥ x0⌋).toNat < Nat.find (hex_m c) := by
        intro hlt
        refine Nat.find_min (hex_m c) hlt ⟨β, hβ, ?_⟩
        omega
      dsimp only [m_c]
      omega
    have h_eq : chvatalClosure P =
        {x | (∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ x ≤ (b i : ℚ)) ∧
             (∀ c : B, (fun j => (c.1 j : ℚ)) ⬝ᵥ x ≤ (m_c c : ℚ))} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hx
        refine ⟨fun i => ?_, fun c => ?_⟩
        · have h := hx (A i) (b i : ℚ) (fun y hy => by rw [hP_eq] at hy; exact hy i)
          simpa using h
        · obtain ⟨β, hβ, hfl⟩ := hm_c_spec c
          have h := hx c.1 β hβ
          rwa [hfl] at h
      · rintro ⟨hxA, hxB⟩ a β hβ
        let β' : ℚ := (β + ((⌊β⌋ : ℚ) + 1)) / 2
        obtain ⟨hfl_β', hlt_β'⟩ := floor_half_add_floor_add_one β
        have hx0_A : ∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ x0 ≤ (b i : ℚ) := by
          have := hx0P; rwa [hP_eq] at this
        have hlt_A : ∀ y : Fin n → ℚ,
            (∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ y ≤ (b i : ℚ)) →
            (fun j => (a j : ℚ)) ⬝ᵥ y < β' := by
          intro y hy
          have hyP : y ∈ P := by rwa [hP_eq]
          exact (hβ y hyP).trans_lt hlt_β'
        obtain ⟨u, hu0, hua, hub⟩ :=
          farkas_dual (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ))
            (fun j => (a j : ℚ)) β' x0 hx0_A hlt_A
        let q_u : Fin k → ℤ := fun i => ⌊u i⌋
        let f_u : Fin k → ℚ := fun i => u i - (q_u i : ℚ)
        have hqu_nonneg : ∀ i, 0 ≤ q_u i := fun i => Int.floor_nonneg.mpr (hu0 i)
        have hfu_nonneg : ∀ i, 0 ≤ f_u i := fun i => sub_nonneg.mpr (Int.floor_le (u i))
        have hfu_lt_one : ∀ i, f_u i < 1 := fun i => by
          dsimp only [f_u, q_u]
          linarith [Int.lt_floor_add_one (u i)]
        let c : Fin n → ℤ := fun j => a j - ∑ i : Fin k, q_u i * A i j
        have hc_eq : ∀ j : Fin n, (c j : ℚ) = ∑ i : Fin k, f_u i * (A i j : ℚ) := by
          intro j
          have hj := congrFun hua j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
          dsimp only [c, f_u]
          push_cast
          rw [← hj, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        have hc_box : c ∈ Box := by
          intro j
          have h1 : |(c j : ℚ)| ≤ (R j : ℚ) := by
            rw [hc_eq j]
            calc
              |∑ i : Fin k, f_u i * (A i j : ℚ)|
                ≤ ∑ i : Fin k, |f_u i * (A i j : ℚ)| := Finset.abs_sum_le_sum_abs _ _
              _ = ∑ i : Fin k, f_u i * |(A i j : ℚ)| := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [abs_mul, abs_of_nonneg (hfu_nonneg i)]
              _ ≤ ∑ i : Fin k, 1 * |(A i j : ℚ)| := by
                refine Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_right (hfu_lt_one i).le (abs_nonneg _)
              _ = (R j : ℚ) := by
                dsimp only [R]; push_cast; simp [Int.cast_abs]
          exact_mod_cast h1
        have hc_valid : ∀ y ∈ P, (fun j => (c j : ℚ)) ⬝ᵥ y ≤ ∑ i : Fin k, f_u i * (b i : ℚ) := by
          intro y hy
          rw [hP_eq] at hy
          have hdot_c : (fun j => (c j : ℚ)) ⬝ᵥ y =
              ∑ i : Fin k, f_u i * ((fun j => (A i j : ℚ)) ⬝ᵥ y) := by
            simp only [dotProduct, hc_eq, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          rw [hdot_c]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hfu_nonneg i)
        let cB : B := ⟨c, hc_box, ∑ i : Fin k, f_u i * (b i : ℚ), hc_valid⟩
        have hmc_le_f : m_c cB ≤ ⌊∑ i : Fin k, f_u i * (b i : ℚ)⌋ :=
          hm_c_le cB _ hc_valid
        have h_ax : (fun j => (a j : ℚ)) ⬝ᵥ x =
            ∑ i : Fin k, (q_u i : ℚ) * ((fun j => (A i j : ℚ)) ⬝ᵥ x) +
            (fun j => (c j : ℚ)) ⬝ᵥ x := by
          have h1 : ∑ i : Fin k, (q_u i : ℚ) * ((fun j => (A i j : ℚ)) ⬝ᵥ x) =
              ∑ j : Fin n, (∑ i : Fin k, (q_u i : ℚ) * (A i j : ℚ)) * x j := by
            simp only [dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
            exact Finset.sum_comm
          rw [h1]
          simp only [dotProduct, c, Int.cast_sub, Int.cast_sum, Int.cast_mul,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        have h_sum_q : ∑ i : Fin k, (q_u i : ℚ) * ((fun j => (A i j : ℚ)) ⬝ᵥ x) ≤
            ∑ i : Fin k, (q_u i : ℚ) * (b i : ℚ) := by
          refine Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hxA i) (by exact_mod_cast hqu_nonneg i)
        have h_cx : (fun j => (c j : ℚ)) ⬝ᵥ x ≤ (⌊∑ i : Fin k, f_u i * (b i : ℚ)⌋ : ℚ) :=
          (hxB cB).trans (Int.cast_le.mpr hmc_le_f)
        have h_ub_split : ∑ i : Fin k, u i * (b i : ℚ) =
            ∑ i : Fin k, f_u i * (b i : ℚ) + ((∑ i : Fin k, q_u i * b i : ℤ) : ℚ) := by
          dsimp only [f_u]
          push_cast
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by ring
        have h_floor_ub : ⌊∑ i : Fin k, u i * (b i : ℚ)⌋ =
            ⌊∑ i : Fin k, f_u i * (b i : ℚ)⌋ + ∑ i : Fin k, q_u i * b i := by
          rw [h_ub_split, Int.floor_add_intCast]
        have h_floor_le : ⌊∑ i : Fin k, u i * (b i : ℚ)⌋ ≤ ⌊β⌋ := by
          rw [← hfl_β']
          exact Int.floor_mono hub.le
        calc
          (fun j => (a j : ℚ)) ⬝ᵥ x
            ≤ ∑ i : Fin k, (q_u i : ℚ) * (b i : ℚ) + (⌊∑ i : Fin k, f_u i * (b i : ℚ)⌋ : ℚ) := by
              linarith [h_ax, h_sum_q, h_cx]
          _ = (⌊∑ i : Fin k, u i * (b i : ℚ)⌋ : ℚ) := by
              rw [h_floor_ub]; push_cast; ring
          _ ≤ (⌊β⌋ : ℚ) := Int.cast_le.mpr h_floor_le
    rw [isPolyhedron_iff_int_system]
    let e : Fin (k + Fintype.card B) ≃ Fin k ⊕ B :=
      (Fintype.equivFin (Fin k ⊕ B)).trans (Equiv.cast (by simp)) |>.symm
    refine ⟨k + Fintype.card B,
      Matrix.of (fun r j => Sum.elim (fun i => A i j) (fun c => c.1 j) (e r)),
      fun r => Sum.elim b m_c (e r), ?_⟩
    rw [h_eq]
    ext x
    simp only [Set.mem_setOf_eq, Matrix.of_apply]
    constructor
    · rintro ⟨h1, h2⟩ r
      rcases h : e r with i | c
      · simpa [h] using h1 i
      · simpa [h] using h2 c
    · intro h
      refine ⟨fun i => ?_, fun c => ?_⟩
      · have := h (e.symm (Sum.inl i))
        simpa using this
      · have := h (e.symm (Sum.inr c))
        simpa using this

private lemma isPolyhedron_inter_ge {n : ℕ} {P : Set (Fin n → ℚ)} (hP : IsPolyhedron P)
    (w : Fin n → ℤ) (m : ℤ) :
    IsPolyhedron (P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)}) := by
  obtain ⟨k, A, b, rfl⟩ := (isPolyhedron_iff_int_system P).mp hP
  rw [isPolyhedron_iff_int_system]
  refine ⟨k + 1,
    Matrix.of (fun r j => Fin.lastCases (-w j) (fun i => A i j) r),
    fun r => Fin.lastCases (-m) b r, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Matrix.of_apply, Fin.forall_fin_succ',
    Fin.lastCases_castSucc, Fin.lastCases_last, Int.cast_neg, ge_iff_le]
  have hneg : (fun j => -(w j : ℚ)) ⬝ᵥ x = -((fun j => (w j : ℚ)) ⬝ᵥ x) := by
    simp [dotProduct]
  rw [hneg, neg_le_neg_iff]

/-! ### Section 5: Face Commuting and Step Lemmas for Chvátal Closure -/

private lemma chvatalClosure_subset_le_sub_one_of_inter_empty {n : ℕ} {P : Set (Fin n → ℚ)}
    (hP : IsPolyhedron P) (w : Fin n → ℤ) (m : ℤ)
    (hemp : P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} = ∅) :
    chvatalClosure P ⊆ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ ((m - 1 : ℤ) : ℚ)} := by
  by_cases hPemp : P = ∅
  · subst hPemp
    rw [chvatalClosure_empty]
    exact Set.empty_subset _
  · obtain ⟨x0, hx0P⟩ := Set.nonempty_iff_ne_empty.mpr hPemp
    obtain ⟨k, A, b, hP_eq⟩ := (isPolyhedron_iff_int_system P).mp hP
    have hx0_A : ∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ x0 ≤ (b i : ℚ) := by
      have := hx0P; rwa [hP_eq] at this
    have hlt : ∀ y : Fin n → ℚ,
        (∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ y ≤ (b i : ℚ)) →
        (fun j => (w j : ℚ)) ⬝ᵥ y < (m : ℚ) := by
      intro y hy
      have hyP : y ∈ P := by rwa [hP_eq]
      by_contra hge
      push_neg at hge
      have hmem : y ∈ P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} := ⟨hyP, hge⟩
      rw [hemp] at hmem
      exact hmem
    obtain ⟨u, hu0, hua, hub⟩ :=
      farkas_dual (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ))
        (fun j => (w j : ℚ)) (m : ℚ) x0 hx0_A hlt
    let β : ℚ := ∑ i : Fin k, u i * (b i : ℚ)
    have hβ_valid : ∀ y ∈ P, (fun j => (w j : ℚ)) ⬝ᵥ y ≤ β := by
      intro y hy
      rw [hP_eq] at hy
      have hdot : (fun j => (w j : ℚ)) ⬝ᵥ y =
          ∑ i : Fin k, u i * ((fun j => (A i j : ℚ)) ⬝ᵥ y) := by
        rw [← hua, sum_dotProduct]
        simp [smul_dotProduct]
      rw [hdot]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hu0 i)
    have hfl_lt : ⌊β⌋ < m := Int.floor_lt.mpr hub
    intro x hx
    have hwx := hx w β hβ_valid
    refine hwx.trans ?_
    exact Int.cast_le.mpr (by omega)

private lemma chvatalClosure_inter_ge_subset {n : ℕ} {P : Set (Fin n → ℚ)}
    (hP : IsPolyhedron P) (w : Fin n → ℤ) (m : ℤ)
    (hP_le : P ⊆ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (m : ℚ)}) :
    chvatalClosure P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} ⊆
      chvatalClosure (P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)}) := by
  set F := P ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)}
  by_cases hFemp : F = ∅
  · have hle := chvatalClosure_subset_le_sub_one_of_inter_empty hP w m hFemp
    rintro x ⟨hxC, hx_ge⟩
    exfalso
    have hx_le : (fun i => (w i : ℚ)) ⬝ᵥ x ≤ ((m - 1 : ℤ) : ℚ) := hle hxC
    have hx_ge' : (m : ℚ) ≤ (fun i => (w i : ℚ)) ⬝ᵥ x := hx_ge
    push_cast at hx_le
    linarith
  · obtain ⟨y0, hy0F⟩ := Set.nonempty_iff_ne_empty.mpr hFemp
    obtain ⟨k, A, b, hP_eq⟩ := (isPolyhedron_iff_int_system P).mp hP
    let aF : Option (Fin k) → Fin n → ℚ := fun o => match o with
      | none => fun j => -(w j : ℚ)
      | some i => fun j => (A i j : ℚ)
    let bF : Option (Fin k) → ℚ := fun o => match o with
      | none => -(m : ℚ)
      | some i => (b i : ℚ)
    have hF_iff : ∀ y : Fin n → ℚ, y ∈ F ↔ ∀ o : Option (Fin k), aF o ⬝ᵥ y ≤ bF o := by
      intro y
      simp only [F, hP_eq, Set.mem_inter_iff, Set.mem_setOf_eq, ge_iff_le]
      constructor
      · rintro ⟨hyA, hyw⟩ o
        cases o with
        | none =>
          change (fun j => -(w j : ℚ)) ⬝ᵥ y ≤ -(m : ℚ)
          have : (fun j => -(w j : ℚ)) = -(fun j => (w j : ℚ)) := rfl
          rw [this, neg_dotProduct, neg_le_neg_iff]
          exact hyw
        | some i => exact hyA i
      · intro h
        refine ⟨fun i => h (some i), ?_⟩
        have h0 := h none
        change (fun j => -(w j : ℚ)) ⬝ᵥ y ≤ -(m : ℚ) at h0
        have : (fun j => -(w j : ℚ)) = -(fun j => (w j : ℚ)) := rfl
        rw [this, neg_dotProduct, neg_le_neg_iff] at h0
        exact h0
    have hy0_F : ∀ o, aF o ⬝ᵥ y0 ≤ bF o := (hF_iff y0).mp hy0F
    rintro x ⟨hxC, hx_ge⟩ a β hβ
    let β' : ℚ := (β + ((⌊β⌋ : ℚ) + 1)) / 2
    obtain ⟨hfl_β', hlt_β'⟩ := floor_half_add_floor_add_one β
    have hlt_F : ∀ y : Fin n → ℚ, (∀ o, aF o ⬝ᵥ y ≤ bF o) →
        (fun j => (a j : ℚ)) ⬝ᵥ y < β' := by
      intro y hy
      exact (hβ y ((hF_iff y).mpr hy)).trans_lt hlt_β'
    obtain ⟨u, hu0, hua, hub⟩ :=
      farkas_dual aF bF (fun j => (a j : ℚ)) β' y0 hy0_F hlt_F
    rw [Fintype.sum_option] at hua hub
    simp only [aF, bF] at hua hub
    let K : ℕ := ⌈u none⌉₊
    have hK_ge : u none ≤ (K : ℚ) := Nat.le_ceil (u none)
    have hK_nonneg : (0 : ℚ) ≤ (K : ℚ) := Nat.cast_nonneg K
    let aK : Fin n → ℤ := fun j => a j + (K : ℤ) * w j
    let βK : ℚ := β' + ((K : ℤ) * m : ℤ)
    have haK_valid : ∀ y ∈ P, (fun j => (aK j : ℚ)) ⬝ᵥ y ≤ βK := by
      intro y hyP
      have hyw : (fun j => (w j : ℚ)) ⬝ᵥ y ≤ (m : ℚ) := hP_le hyP
      have hyA : ∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ y ≤ (b i : ℚ) := by
        rwa [hP_eq] at hyP
      have hdot_a : (fun j => (a j : ℚ)) ⬝ᵥ y =
          -(u none * ((fun j => (w j : ℚ)) ⬝ᵥ y)) +
          ∑ i : Fin k, u (some i) * ((fun j => (A i j : ℚ)) ⬝ᵥ y) := by
        rw [← hua, add_dotProduct, smul_dotProduct, sum_dotProduct]
        have : (fun j => -(w j : ℚ)) = -(fun j => (w j : ℚ)) := rfl
        rw [this, neg_dotProduct]
        simp [smul_dotProduct, smul_eq_mul]
      have hsum_A : ∑ i : Fin k, u (some i) * ((fun j => (A i j : ℚ)) ⬝ᵥ y) ≤
          ∑ i : Fin k, u (some i) * (b i : ℚ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyA i) (hu0 (some i))
      have hdot_aK : (fun j => (aK j : ℚ)) ⬝ᵥ y =
          (fun j => (a j : ℚ)) ⬝ᵥ y + (K : ℚ) * ((fun j => (w j : ℚ)) ⬝ᵥ y) := by
        simp only [dotProduct, aK]
        push_cast
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      rw [hdot_aK, hdot_a]
      have hdiff_nonpos : ((K : ℚ) - u none) * (((fun j => (w j : ℚ)) ⬝ᵥ y) - (m : ℚ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      dsimp only [βK]
      push_cast
      linarith
    have hx_aK := hxC aK βK haK_valid
    have hfl_βK : ⌊βK⌋ = ⌊β⌋ + (K : ℤ) * m := by
      dsimp only [βK]
      rw [Int.floor_add_intCast, hfl_β']
    have hdot_x : (fun j => (aK j : ℚ)) ⬝ᵥ x =
        (fun j => (a j : ℚ)) ⬝ᵥ x + (K : ℚ) * ((fun j => (w j : ℚ)) ⬝ᵥ x) := by
      simp only [dotProduct, aK]
      push_cast
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [hdot_x, hfl_βK] at hx_aK
    push_cast at hx_aK
    have hKw : (K : ℚ) * (m : ℚ) ≤ (K : ℚ) * ((fun j => (w j : ℚ)) ⬝ᵥ x) :=
      mul_le_mul_of_nonneg_left hx_ge hK_nonneg
    linarith

private lemma chvatalIter_poly_and_inter_ge {n : ℕ} (t : ℕ) {S : Set (Fin n → ℚ)}
    (hS : IsPolyhedron S) (w : Fin n → ℤ) (m : ℤ)
    (hS_le : S ⊆ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (m : ℚ)}) :
    IsPolyhedron (chvatalIter t S) ∧
    chvatalIter t S ⊆ S ∧
    chvatalIter t S ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} ⊆
      chvatalIter t (S ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)}) := by
  induction t with
  | zero =>
    exact ⟨hS, Set.Subset.rfl, Set.Subset.rfl⟩
  | succ t ih =>
    obtain ⟨ht_poly, ht_sub, ht_inter⟩ := ih
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply] at ht_poly ht_sub ht_inter ⊢
    have ht_le : (chvatalClosure)^[t] S ⊆ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (m : ℚ)} :=
      ht_sub.trans hS_le
    refine ⟨isPolyhedron_chvatalClosure ht_poly,
      (chvatalClosure_subset_self_of_isPolyhedron ht_poly).trans ht_sub, ?_⟩
    exact (chvatalClosure_inter_ge_subset ht_poly w m ht_le).trans (chvatalClosure_mono ht_inter)

/-! ### Section 6: Integral affine maps, lattice bases, and the dimension reduction -/

private lemma intDot_mulVec {n k : ℕ} (U : Matrix (Fin k) (Fin n) ℤ) (a : Fin k → ℤ)
    (x : Fin n → ℚ) :
    (fun i => (a i : ℚ)) ⬝ᵥ (U.map (Int.cast : ℤ → ℚ) *ᵥ x) =
      (fun j => ((a ᵥ* U) j : ℚ)) ⬝ᵥ x := by
  rw [dotProduct_mulVec]
  congr 1
  ext j
  simp [vecMul, dotProduct]

private lemma image_chvatalClosure_subset {n k : ℕ} (U : Matrix (Fin k) (Fin n) ℤ)
    (S : Set (Fin n → ℚ)) :
    (fun x => U.map (Int.cast : ℤ → ℚ) *ᵥ x) '' chvatalClosure S ⊆
      chvatalClosure ((fun x => U.map (Int.cast : ℤ → ℚ) *ᵥ x) '' S) := by
  rintro _ ⟨x, hx, rfl⟩ a β hβ
  rw [intDot_mulVec]
  apply hx (a ᵥ* U) β
  intro y hy
  rw [← intDot_mulVec]
  exact hβ _ ⟨y, hy, rfl⟩

private lemma image_chvatalIter_subset {n k : ℕ} (U : Matrix (Fin k) (Fin n) ℤ) (t : ℕ)
    (S : Set (Fin n → ℚ)) :
    (fun x => U.map (Int.cast : ℤ → ℚ) *ᵥ x) '' chvatalIter t S ⊆
      chvatalIter t ((fun x => U.map (Int.cast : ℤ → ℚ) *ᵥ x) '' S) := by
  induction t with
  | zero => exact Set.Subset.rfl
  | succ t ih =>
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply] at ih ⊢
    exact (image_chvatalClosure_subset U _).trans (chvatalClosure_mono ih)

private lemma chvatalIter_empty {n : ℕ} (t : ℕ) :
    chvatalIter t (∅ : Set (Fin n → ℚ)) = ∅ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply] at ih ⊢
    rw [ih, chvatalClosure_empty]

private lemma chvatalIter_eq_empty_mono {n : ℕ} {S : Set (Fin n → ℚ)} {t t' : ℕ}
    (h : chvatalIter t S = ∅) (htt : t ≤ t') : chvatalIter t' S = ∅ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htt
  rw [add_comm, chvatalIter_add, h, chvatalIter_empty]

private lemma isPolyhedron_convex {n : ℕ} {P : Set (Fin n → ℚ)} (hP : IsPolyhedron P) :
    Convex ℚ P := by
  obtain ⟨k, D, d, rfl⟩ := hP
  intro x hx y hy u v hu hv huv i
  have hxi := hx i
  have hyi := hy i
  have hlin : (D *ᵥ (u • x + v • y)) i = u * (D *ᵥ x) i + v * (D *ᵥ y) i := by
    simp [mulVec_add, mulVec_smul]
  rw [hlin]
  calc
    u * (D *ᵥ x) i + v * (D *ᵥ y) i ≤ u * d i + v * d i := by nlinarith
    _ = (u + v) * d i := by ring
    _ = d i := by rw [huv, one_mul]

/-- A nonzero integral vector is a nonzero multiple of a member of some lattice basis. -/
private lemma exists_basis_smul {n : ℕ} (w : Fin n → ℤ) (hw : w ≠ 0) :
    ∃ (bM : Module.Basis (Fin n) ℤ (Fin n → ℤ)) (j : Fin n) (e : ℤ), e ≠ 0 ∧ w = e • bM j := by
  classical
  set N : Submodule ℤ (Fin n → ℤ) := Submodule.span ℤ {w}
  obtain ⟨o, snf⟩ := Submodule.smithNormalForm (Pi.basisFun ℤ (Fin n)) N
  have hwN : w ∈ N := Submodule.mem_span_singleton_self w
  have ho : 0 < o := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · subst h0
      exfalso
      have : (⟨w, hwN⟩ : N) = 0 := by
        apply snf.bN.repr.injective
        ext i; exact i.elim0
      exact hw (congrArg Subtype.val this)
    · exact h0
  let i0 : Fin o := ⟨0, ho⟩
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (snf.bN i0).2
  have hsnf := snf.snf i0
  have hrep := snf.repr_apply_embedding_eq_repr_smul ⟨w, hwN⟩ (i := i0)
  set c := snf.bN.repr ⟨w, hwN⟩ i0
  have hrep' : snf.bM.repr w (snf.f i0) = snf.a i0 * c := by
    rw [hrep, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have ha0 : snf.a i0 ≠ 0 := by
    intro h
    have : (snf.bN i0 : Fin n → ℤ) = 0 := by rw [hsnf, h, zero_smul]
    exact snf.bN.ne_zero i0 (Subtype.ext this)
  -- apply the coordinate functional at `f i0` to `a • bM (f i0) = d • w`
  have key : snf.a i0 = d * (snf.a i0 * c) := by
    have h1 : snf.bM.repr (snf.a i0 • snf.bM (snf.f i0)) (snf.f i0) =
        snf.bM.repr (d • w) (snf.f i0) := by rw [← hsnf, hd]
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at h1
    exact h1.trans (by rw [hrep'])
  have hdc : d * c = 1 := by
    have : snf.a i0 * 1 = snf.a i0 * (d * c) := by rw [mul_one]; linear_combination key
    exact (mul_left_cancel₀ ha0 this).symm
  have hdd : d * d = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdc with h | h <;> simp [h]
  refine ⟨snf.bM, snf.f i0, d * snf.a i0, mul_ne_zero (left_ne_zero_of_mul_eq_one hdc) ha0, ?_⟩
  rw [mul_smul, ← hsnf, ← hd, smul_smul, hdd, one_smul]

private lemma isIntegral_intMat_mulVec {a b : ℕ} (Y : Matrix (Fin a) (Fin b) ℤ)
    {z : Fin b → ℚ} (hz : IsIntegral z) : IsIntegral (Y.map (Int.cast : ℤ → ℚ) *ᵥ z) := by
  choose f hf using hz
  intro i
  exact ⟨∑ s, Y i s * f s, by simp [mulVec, dotProduct, hf]⟩

private lemma isIntegral_insertNth {k : ℕ} (j : Fin (k + 1)) (c : ℤ) {y : Fin k → ℚ}
    (hy : IsIntegral y) : IsIntegral (Fin.insertNth j (c : ℚ) y) := by
  intro r
  refine Fin.succAboveCases j ?_ (fun i => ?_) r
  · exact ⟨c, by simp⟩
  · obtain ⟨t, ht⟩ := hy i
    exact ⟨t, by simp [ht]⟩

private lemma isPolyhedron_preimage_insertNth {k : ℕ} (j : Fin (k + 1)) (c : ℚ)
    (Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) {F : Set (Fin (k + 1) → ℚ)}
    (hF : IsPolyhedron F) : IsPolyhedron {y : Fin k → ℚ | Y *ᵥ Fin.insertNth j c y ∈ F} := by
  obtain ⟨p, D, d, rfl⟩ := hF
  refine ⟨p, Matrix.of fun r i => (D * Y) r (j.succAbove i),
    fun r => d r - (D * Y) r j * c, ?_⟩
  ext y
  simp only [Set.mem_setOf_eq, Pi.le_def, mulVec_mulVec]
  refine forall_congr' fun r => ?_
  simp only [mulVec, dotProduct, Fin.sum_univ_succAbove _ j, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, Matrix.of_apply]
  constructor <;> intro h <;> linarith

/-- Dimension reduction: a lattice-free polyhedron lying in a hyperplane `v x = m'`, where `v`
is a member of a lattice basis, inherits the closure bound of dimension one less. -/
private lemma chvatalIter_eq_empty_of_hyperplane {k : ℕ} (γ : ℕ)
    (IH : ∀ G : Set (Fin k → ℚ), IsPolyhedron G → (∀ x ∈ G, ¬ IsIntegral x) →
      chvatalIter γ G = ∅)
    (bM : Module.Basis (Fin (k + 1)) ℤ (Fin (k + 1) → ℤ)) (j : Fin (k + 1)) (m' : ℤ)
    (F : Set (Fin (k + 1) → ℚ)) (hF : IsPolyhedron F) (hFZ : ∀ x ∈ F, ¬ IsIntegral x)
    (hFH : ∀ x ∈ F, (fun i => (bM j i : ℚ)) ⬝ᵥ x = m') : chvatalIter γ F = ∅ := by
  classical
  let Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ := Matrix.of fun r i => bM r i
  let Y : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    Matrix.of fun i r => bM.repr (Pi.single i 1) r
  have hYZ : Y * Z = 1 := by
    ext i i'
    have h := congrFun (bM.sum_repr (Pi.single i 1)) i'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [Y, Z, Matrix.mul_apply, Matrix.of_apply, h, Matrix.one_apply, Pi.single_apply]
    by_cases hii : i = i' <;> simp [hii, eq_comm]
  have hZY : Z * Y = 1 := mul_eq_one_comm.mp hYZ
  set Yq := Y.map (Int.cast : ℤ → ℚ)
  set Zq := Z.map (Int.cast : ℤ → ℚ)
  have hYZq : Yq * Zq = 1 := by
    show Y.map (Int.castRingHom ℚ) * Z.map (Int.castRingHom ℚ) = 1
    rw [← Matrix.map_mul, hYZ]; simp
  have hZYq : Zq * Yq = 1 := by
    show Z.map (Int.castRingHom ℚ) * Y.map (Int.castRingHom ℚ) = 1
    rw [← Matrix.map_mul, hZY]; simp
  let U : Matrix (Fin k) (Fin (k + 1)) ℤ := Matrix.of fun i s => bM (j.succAbove i) s
  let π : (Fin (k + 1) → ℚ) → (Fin k → ℚ) := fun x => U.map (Int.cast : ℤ → ℚ) *ᵥ x
  have hπ : ∀ x i, π x i = (Zq *ᵥ x) (j.succAbove i) := by
    intro x i; simp [π, U, Zq, Z, mulVec, dotProduct]
  have hZx : ∀ x ∈ F, Zq *ᵥ x = Fin.insertNth j (m' : ℚ) (π x) := by
    intro x hx
    ext r
    refine Fin.succAboveCases j ?_ (fun i => ?_) r
    · rw [Fin.insertNth_apply_same, ← hFH x hx]
      simp [Zq, Z, mulVec, dotProduct]
    · rw [Fin.insertNth_apply_succAbove, hπ]
  have hYZx : ∀ x, Yq *ᵥ (Zq *ᵥ x) = x := by
    intro x; rw [mulVec_mulVec, hYZq, one_mulVec]
  have hG_eq : π '' F = {y | Yq *ᵥ Fin.insertNth j (m' : ℚ) y ∈ F} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show Yq *ᵥ Fin.insertNth j (m' : ℚ) (π x) ∈ F
      rw [← hZx x hx, hYZx]; exact hx
    · intro hy
      refine ⟨_, hy, ?_⟩
      ext i
      rw [hπ, mulVec_mulVec, hZYq, one_mulVec, Fin.insertNth_apply_succAbove]
  have hG_poly : IsPolyhedron (π '' F) := by
    rw [hG_eq]; exact isPolyhedron_preimage_insertNth j _ Yq hF
  have hG_free : ∀ y ∈ π '' F, ¬ IsIntegral y := by
    rintro _ ⟨x, hx, rfl⟩ hy
    apply hFZ x hx
    have h1 : IsIntegral (Zq *ᵥ x) := by rw [hZx x hx]; exact isIntegral_insertNth j m' hy
    have h2 := isIntegral_intMat_mulVec Y h1
    rwa [hYZx] at h2
  have hG := IH _ hG_poly hG_free
  have himg := image_chvatalIter_subset U γ F
  rw [hG, Set.subset_empty_iff, Set.image_eq_empty] at himg
  exact himg

/-! ### Section 7: The one-dimensional case and the arithmetic of the recursion -/

private lemma exists_mem_coord_eq {P : Set (Fin 1 → ℚ)} (hP : IsPolyhedron P)
    {x y : Fin 1 → ℚ} (hx : x ∈ P) (hy : y ∈ P) {c : ℚ} (h1 : x 0 ≤ c) (h2 : c ≤ y 0) :
    ∃ z ∈ P, z 0 = c := by
  rcases eq_or_lt_of_le (h1.trans h2) with heq | hlt
  · exact ⟨x, hx, le_antisymm h1 (heq ▸ h2)⟩
  · set t := (c - x 0) / (y 0 - x 0)
    have hpos : 0 < y 0 - x 0 := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
    have ht1 : t ≤ 1 := (div_le_one hpos).mpr (by linarith)
    refine ⟨x + t • (y - x), (isPolyhedron_convex hP).add_smul_sub_mem hx hy ⟨ht0, ht1⟩, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, t]
    field_simp
    ring

private lemma chvatalIter_two_eq_empty_dim_one (P : Set (Fin 1 → ℚ)) (hP : IsPolyhedron P)
    (hPZ : ∀ x ∈ P, ¬ IsIntegral x) : chvatalIter 2 P = ∅ := by
  by_cases hPe : P = ∅
  · rw [hPe, chvatalIter_empty]
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hPe
  have hint : ∀ z : Fin 1 → ℚ, ∀ t : ℤ, z 0 = t → IsIntegral z := by
    intro z t ht i
    fin_cases i
    exact ⟨t, ht⟩
  set k := ⌊x0 0⌋
  have hk1 : (k : ℚ) ≤ x0 0 := Int.floor_le _
  have hk2 : x0 0 < k + 1 := Int.lt_floor_add_one _
  have hbetween : ∀ x ∈ P, (k : ℚ) < x 0 ∧ x 0 < k + 1 := by
    intro x hx
    constructor
    · by_contra hc
      push_neg at hc
      obtain ⟨z, hz, hz0⟩ := exists_mem_coord_eq hP hx hx0 hc hk1
      exact hPZ z hz (hint z k hz0)
    · by_contra hc
      push_neg at hc
      obtain ⟨z, hz, hz0⟩ := exists_mem_coord_eq hP hx0 hx hk2.le hc
      exact hPZ z hz (hint z (k + 1) (by rw [hz0]; push_cast; ring))
  have hdot1 : ∀ x : Fin 1 → ℚ, (fun i => (((fun _ => (1 : ℤ)) i : ℤ) : ℚ)) ⬝ᵥ x = x 0 := by
    intro x; simp [dotProduct]
  have hdot2 : ∀ x : Fin 1 → ℚ, (fun i => (((fun _ => (-1 : ℤ)) i : ℤ) : ℚ)) ⬝ᵥ x = -x 0 := by
    intro x; simp [dotProduct]
  have e1 : P ∩ {x | (fun i => (((fun _ => (1 : ℤ)) i : ℤ) : ℚ)) ⬝ᵥ x ≥ ((k + 1 : ℤ) : ℚ)} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      hdot1, not_le]
    intro hx; have := (hbetween x hx).2; push_cast; linarith
  have e2 : P ∩ {x | (fun i => (((fun _ => (-1 : ℤ)) i : ℤ) : ℚ)) ⬝ᵥ x ≥ ((-k : ℤ) : ℚ)} = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and,
      hdot2, not_le]
    intro hx; have := (hbetween x hx).1; push_cast; linarith
  have h1 := chvatalClosure_subset_le_sub_one_of_inter_empty hP _ _ e1
  have h2 := chvatalClosure_subset_le_sub_one_of_inter_empty hP _ _ e2
  have hC : chvatalIter 1 P = ∅ := by
    show chvatalClosure P = ∅
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have a1 := h1 hx
    have a2 := h2 hx
    simp only [Set.mem_setOf_eq, hdot1, hdot2] at a1 a2
    push_cast at a1 a2
    linarith
  exact chvatalIter_eq_empty_mono hC (by norm_num)

private lemma recursion_arith (k : ℕ) :
    (2 * ((k + 2) * (k + 3) * 2 ^ ((k + 2) ^ 2)) + 1) *
        ((k + 1) ^ (2 * (k + 1)) * 2 ^ ((k + 1) ^ 3) + 1) ≤
      (k + 2) ^ (2 * (k + 2)) * 2 ^ ((k + 2) ^ 3) := by
  set A := (k + 1) ^ (2 * (k + 1)) with hA
  set B := 2 ^ ((k + 1) ^ 3) with hB
  set C := 2 ^ ((k + 2) ^ 2) with hC
  have hA1 : 1 ≤ A := Nat.one_le_pow _ _ (by omega)
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ (by omega)
  have hC1 : 1 ≤ C := Nat.one_le_pow _ _ (by omega)
  have h1 : A * B + 1 ≤ 2 * (A * B) := by nlinarith
  have h2 : 2 * ((k + 2) * (k + 3) * C) + 1 ≤ (k + 2) ^ 2 * (4 * C) := by
    have e : (k + 2) ^ 2 * (4 * C) = 2 * ((k + 2) * (k + 3) * C) + (k + 2) * (2 * k + 2) * C := by
      ring
    have hp : 1 ≤ (k + 2) * (2 * k + 2) * C :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have h3 : (k + 2) ^ 2 * A ≤ (k + 2) ^ (2 * (k + 2)) := by
    have : A ≤ (k + 2) ^ (2 * (k + 1)) := Nat.pow_le_pow_left (by omega) _
    calc (k + 2) ^ 2 * A ≤ (k + 2) ^ 2 * (k + 2) ^ (2 * (k + 1)) := Nat.mul_le_mul_left _ this
      _ = (k + 2) ^ (2 * (k + 2)) := by rw [← pow_add]; congr 1; ring
  have h4 : 8 * (C * B) ≤ 2 ^ ((k + 2) ^ 3) := by
    have : 8 * (C * B) = 2 ^ (3 + (k + 2) ^ 2 + (k + 1) ^ 3) := by
      rw [pow_add, pow_add]; norm_num [hB, hC]; ring
    rw [this]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  calc (2 * ((k + 2) * (k + 3) * C) + 1) * (A * B + 1)
      ≤ ((k + 2) ^ 2 * (4 * C)) * (2 * (A * B)) := Nat.mul_le_mul h2 h1
    _ = ((k + 2) ^ 2 * A) * (8 * (C * B)) := by ring
    _ ≤ (k + 2) ^ (2 * (k + 2)) * 2 ^ ((k + 2) ^ 3) := Nat.mul_le_mul h3 h4

/-! ### Section 8: The induction step (dimension `k + 2`) -/

private lemma chvatalIter_eq_empty_step (k γ' : ℕ)
    (IH : ∀ G : Set (Fin (k + 1) → ℚ), IsPolyhedron G → (∀ x ∈ G, ¬ IsIntegral x) →
      chvatalIter γ' G = ∅)
    (P : Set (Fin (k + 2) → ℚ)) (hP : IsPolyhedron P) (hPZ : ∀ x ∈ P, ¬ IsIntegral x) :
    chvatalIter ((2 * ((k + 2) * (k + 3) * 2 ^ ((k + 2) ^ 2)) + 1) * (γ' + 1)) P = ∅ := by
  set Dn : ℕ := (k + 2) * (k + 3) * 2 ^ ((k + 2) ^ 2) with hDn
  by_cases hPe : P = ∅
  · rw [hPe, chvatalIter_empty]
  obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hPe
  obtain ⟨w, hw0, hflat⟩ :=
    exists_flat_direction_of_no_integer_point (n := k + 2) (by omega) P hP hPZ
  obtain ⟨bM, j, e, he, hwe⟩ := exists_basis_smul w hw0
  set vq : Fin (k + 2) → ℚ := fun i => (bM j i : ℚ) with hvq
  -- the flatness bound transferred to the basis vector `v = bM j`
  have hbound_real : ((((k + 2) * (k + 2 + 1) : ℕ) : ℝ)) * (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) ^ 2 / 2)
      ≤ (Dn : ℝ) := by
    have hpow : (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ) ^ 2 / 2) ≤ (2 : ℝ) ^ (((k + 2) ^ 2 : ℕ) : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ ((k : ℝ) + 2) ^ 2 := by positivity
      push_cast; linarith
    rw [Real.rpow_natCast] at hpow
    rw [hDn]
    push_cast at hpow ⊢
    have hpos : (0 : ℝ) ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) := by positivity
    calc ((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * (2 : ℝ) ^ (((k : ℝ) + 2) ^ 2 / 2)
        ≤ ((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * (2 : ℝ) ^ ((k + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hpos
      _ = ((k : ℝ) + 2) * ((k : ℝ) + 3) * 2 ^ ((k + 2) ^ 2) := by ring
  have hv : ∀ x ∈ P, ∀ x' ∈ P, |vq ⬝ᵥ (x - x')| ≤ (Dn : ℚ) := by
    intro x hx x' hx'
    have h := hflat x hx x' hx'
    have hwq : (fun i => (w i : ℚ)) = (e : ℚ) • vq := by
      ext i; rw [hwe]; simp [hvq]
    rw [hwq, smul_dotProduct, smul_eq_mul] at h
    have he1 : (1 : ℚ) ≤ |(e : ℚ)| := by
      have : (1 : ℤ) ≤ |e| := Int.one_le_abs he
      exact_mod_cast this
    have h' : ((|(e : ℚ) * (vq ⬝ᵥ (x - x'))| : ℚ) : ℝ) ≤ (Dn : ℝ) := by
      rw [Rat.cast_abs]; exact h.trans hbound_real
    have h'' : |(e : ℚ) * (vq ⬝ᵥ (x - x'))| ≤ (Dn : ℚ) := by exact_mod_cast h'
    rw [abs_mul] at h''
    have hnn : 0 ≤ |vq ⬝ᵥ (x - x')| := abs_nonneg _
    nlinarith
  have hsub : ∀ x x' : Fin (k + 2) → ℚ, vq ⬝ᵥ (x - x') = vq ⬝ᵥ x - vq ⬝ᵥ x' :=
    fun x x' => dotProduct_sub _ _ _
  set m0 : ℤ := ⌈vq ⬝ᵥ x0⌉ + Dn with hm0
  have hP_le : P ⊆ {x | vq ⬝ᵥ x ≤ (m0 : ℚ)} := by
    intro x hx
    have h := (abs_le.mp (hv x hx x0 hx0)).2
    rw [hsub] at h
    have := Int.le_ceil (vq ⬝ᵥ x0)
    show vq ⬝ᵥ x ≤ ((⌈vq ⬝ᵥ x0⌉ + (Dn : ℤ) : ℤ) : ℚ)
    push_cast; linarith
  have hP_ge : ∀ x ∈ P, vq ⬝ᵥ x0 - Dn ≤ vq ⬝ᵥ x := by
    intro x hx
    have h := (abs_le.mp (hv x hx x0 hx0)).1
    rw [hsub] at h
    linarith
  -- block induction
  have hblock : ∀ t : ℕ, IsPolyhedron (chvatalIter (t * (γ' + 1)) P) ∧
      chvatalIter (t * (γ' + 1)) P ⊆ P ∧
      chvatalIter (t * (γ' + 1)) P ⊆ {x | vq ⬝ᵥ x ≤ ((m0 - (t : ℤ) : ℤ) : ℚ)} := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.zero_mul, Nat.cast_zero, sub_zero]
      exact ⟨hP, Set.Subset.rfl, hP_le⟩
    | succ t ih =>
      obtain ⟨hQ, hQP, hQle⟩ := ih
      set Q := chvatalIter (t * (γ' + 1)) P with hQdef
      set m : ℤ := m0 - (t : ℤ)
      set F := Q ∩ {x | (fun i => (bM j i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} with hFdef
      have hF : IsPolyhedron F := isPolyhedron_inter_ge hQ (bM j) m
      have hFZ : ∀ x ∈ F, ¬ IsIntegral x := fun x hx => hPZ x (hQP hx.1)
      have hFH : ∀ x ∈ F, (fun i => (bM j i : ℚ)) ⬝ᵥ x = m :=
        fun x hx => le_antisymm (hQle hx.1) hx.2
      have hFe : chvatalIter γ' F = ∅ :=
        chvatalIter_eq_empty_of_hyperplane γ' IH bM j m F hF hFZ hFH
      obtain ⟨hp, hs, hi⟩ := chvatalIter_poly_and_inter_ge γ' hQ (bM j) m hQle
      have hemp : chvatalIter γ' Q ∩ {x | (fun i => (bM j i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} = ∅ := by
        rw [← Set.subset_empty_iff, ← hFe]; exact hi
      have hstep := chvatalClosure_subset_le_sub_one_of_inter_empty hp (bM j) m hemp
      have heq : chvatalIter ((t + 1) * (γ' + 1)) P = chvatalClosure (chvatalIter γ' Q) := by
        have : (t + 1) * (γ' + 1) = 1 + (γ' + t * (γ' + 1)) := by ring
        rw [this, chvatalIter_add, chvatalIter_add]
        rfl
      rw [heq]
      refine ⟨isPolyhedron_chvatalClosure hp,
        (chvatalClosure_subset_self_of_isPolyhedron hp).trans (hs.trans hQP), ?_⟩
      have hm1 : ((m - 1 : ℤ) : ℚ) = ((m0 - ((t + 1 : ℕ) : ℤ) : ℤ) : ℚ) := by
        simp only [m]; push_cast; ring
      rw [← hm1]
      exact hstep
  obtain ⟨_, hQP, hQle⟩ := hblock (2 * Dn + 1)
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have h1 := hQle hx
  have h2 := hP_ge x (hQP hx)
  have h3 := Int.ceil_lt_add_one (vq ⬝ᵥ x0)
  simp only [Set.mem_setOf_eq, hm0] at h1
  push_cast at h1
  linarith

/-! ### Section 9: Main theorem (Cook–Coullard–Turán, CGST Theorem 8) -/

theorem solution {n : ℕ} (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∀ x ∈ P, ¬ IsIntegral x) :
    chvatalIter (n ^ (2 * n) * 2 ^ (n ^ 3)) P = ∅ := by
  have key : ∀ k : ℕ, ∀ P : Set (Fin (k + 1) → ℚ), IsPolyhedron P →
      (∀ x ∈ P, ¬ IsIntegral x) →
      chvatalIter ((k + 1) ^ (2 * (k + 1)) * 2 ^ ((k + 1) ^ 3)) P = ∅ := by
    intro k
    induction k with
    | zero =>
      intro P hP hPZ
      simpa using chvatalIter_two_eq_empty_dim_one P hP hPZ
    | succ k ih =>
      intro P hP hPZ
      exact chvatalIter_eq_empty_mono (chvatalIter_eq_empty_step k _ ih P hP hPZ)
        (recursion_arith k)
  rcases n with _ | k
  · have : P = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      exact hPZ x hx (fun i => i.elim0)
    rw [this, chvatalIter_empty]
  · exact key k P hP hPZ
