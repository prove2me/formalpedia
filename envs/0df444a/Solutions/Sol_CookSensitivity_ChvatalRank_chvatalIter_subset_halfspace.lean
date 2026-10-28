-- Prove2me | solution 1 for CookSensitivity.ChvatalRank.chvatalIter_subset_halfspace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:02:00.807377+00:00
-- url     : https://prove2.me/submissions/3f5bcbe2-2049-4bc7-87b8-2efaaec092d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CookSensitivity_ChvatalRank_IntegerProgram
import Definitions.Def_CookSensitivity_ChvatalRank_ChvatalClosure
import Theorems.Thm_CookSensitivity_ChvatalRank_chvatalIter_eq_empty_of_no_integer_point

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

private lemma chvatalIter_step_block {n : ℕ} {P S : Set (Fin n → ℚ)}
    (hS : IsPolyhedron S) (hSP : S ⊆ P)
    (w : Fin n → ℤ) (q m : ℤ)
    (hq : IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' integerHull P) (q : ℚ))
    (hqm : q < m)
    (hS_le : S ⊆ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (m : ℚ)}) :
    IsPolyhedron (chvatalIter (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) S) ∧
    chvatalIter (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) S ⊆ P ∧
    chvatalIter (n ^ (2 * n) * 2 ^ (n ^ 3) + 1) S ⊆
      {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ ((m - 1 : ℤ) : ℚ)} := by
  set N := n ^ (2 * n) * 2 ^ (n ^ 3)
  set F := S ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)}
  have hF_poly : IsPolyhedron F := isPolyhedron_inter_ge hS w m
  have hF_no_int : ∀ z ∈ F, ¬ IsIntegral z := by
    rintro z ⟨hzS, hzm⟩ hzI
    have hzP : z ∈ P := hSP hzS
    have hz_hull : z ∈ integerHull P := subset_convexHull ℚ _ ⟨hzP, hzI⟩
    have hzq : (fun i => (w i : ℚ)) ⬝ᵥ z ≤ (q : ℚ) := hq.2 ⟨z, hz_hull, rfl⟩
    have hqm' : (q : ℚ) < (m : ℚ) := Int.cast_lt.mpr hqm
    have hzm' : (m : ℚ) ≤ (fun i => (w i : ℚ)) ⬝ᵥ z := hzm
    linarith
  have hFN_empty : chvatalIter N F = ∅ :=
    chvatalIter_eq_empty_of_no_integer_point F hF_poly hF_no_int
  obtain ⟨hSN_poly, hSN_sub, hSN_inter⟩ := chvatalIter_poly_and_inter_ge N hS w m hS_le
  have hSN_inter_empty : chvatalIter N S ∩ {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≥ (m : ℚ)} = ∅ := by
    rw [← Set.subset_empty_iff, ← hFN_empty]
    exact hSN_inter
  have hstep_eq : chvatalIter (N + 1) S = chvatalClosure (chvatalIter N S) := by
    simp only [chvatalIter, Function.iterate_succ', Function.comp_apply]
  rw [hstep_eq]
  refine ⟨isPolyhedron_chvatalClosure hSN_poly,
    (chvatalClosure_subset_self_of_isPolyhedron hSN_poly).trans (hSN_sub.trans hSP),
    chvatalClosure_subset_le_sub_one_of_inter_empty hSN_poly w m hSN_inter_empty⟩

/-! ### Section 6: Existence of the LP Optimum `μ` -/

private theorem exists_lp_greatest {n : ℕ} (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∃ x ∈ P, IsIntegral x)
    (w : Fin n → ℤ) (q : ℤ)
    (hq : IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' integerHull P) (q : ℚ)) :
    ∃ μ : ℚ, IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' P) μ := by
  obtain ⟨x0, hx0P, hx0I⟩ := hPZ
  obtain ⟨k, A, b, hP_eq⟩ := (isPolyhedron_iff_int_system P).mp hP
  let w_Q : Fin n → ℚ := fun j => (w j : ℚ)
  -- Step 1: Every recession ray `v` (`A v ≤ 0`) satisfies `w_Q ⬝ᵥ v ≤ 0`.
  have hrec : ∀ v : Fin n → ℚ,
      (∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ v ≤ 0) → w_Q ⬝ᵥ v < 1 := by
    intro v hv
    by_contra hge
    push_neg at hge
    let M : ℕ := ∏ j : Fin n, (v j).den
    have hM_pos : 0 < M := Finset.prod_pos fun j _ => (v j).pos
    have hM_pos_Q : (0 : ℚ) < (M : ℚ) := Nat.cast_pos.mpr hM_pos
    let u : Fin n → ℚ := (M : ℚ) • v
    have huI : IsIntegral u := by
      intro j
      apply rat_mul_nat_eq_int
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have huA : ∀ i : Fin k, (fun j => (A i j : ℚ)) ⬝ᵥ u ≤ 0 := by
      intro i
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hM_pos_Q.le (hv i)
    have huw : (1 : ℚ) ≤ w_Q ⬝ᵥ u := by
      rw [dotProduct_smul, smul_eq_mul]
      have hM1 : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast hM_pos
      nlinarith
    let T : ℕ := (q - ⌊w_Q ⬝ᵥ x0⌋).toNat + 1
    let z : Fin n → ℚ := x0 + (T : ℚ) • u
    have hzI : IsIntegral z := isIntegral_add hx0I (isIntegral_natSmul T huI)
    have hzP : z ∈ P := by
      rw [hP_eq]
      intro i
      have hx0A : (fun j => (A i j : ℚ)) ⬝ᵥ x0 ≤ (b i : ℚ) := by
        have hmem := hx0P
        rw [hP_eq] at hmem
        exact hmem i
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
      have hTu : (T : ℚ) * ((fun j => (A i j : ℚ)) ⬝ᵥ u) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg T) (huA i)
      linarith
    have hz_hull : z ∈ integerHull P := subset_convexHull ℚ _ ⟨hzP, hzI⟩
    have hzq : w_Q ⬝ᵥ z ≤ (q : ℚ) := hq.2 ⟨z, hz_hull, rfl⟩
    have hzw : w_Q ⬝ᵥ z = w_Q ⬝ᵥ x0 + (T : ℚ) * (w_Q ⬝ᵥ u) := by
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hT_gt : (q : ℚ) - w_Q ⬝ᵥ x0 < (T : ℚ) := by
      have hfl : (⌊w_Q ⬝ᵥ x0⌋ : ℚ) ≤ w_Q ⬝ᵥ x0 := Int.floor_le _
      have hT_int : q - ⌊w_Q ⬝ᵥ x0⌋ < (T : ℤ) := by dsimp only [T]; omega
      have hT_rat : ((q - ⌊w_Q ⬝ᵥ x0⌋ : ℤ) : ℚ) < (T : ℚ) := by exact_mod_cast hT_int
      push_cast at hT_rat
      linarith
    nlinarith
  -- Step 2: By `farkas_dual` on `{v | A v ≤ 0}`, `w_Q` is a nonnegative combination of rows of `A`,
  -- giving an upper bound `B` for `w_Q ⬝ᵥ x` on `P`.
  obtain ⟨u_dual, hu_dual0, hu_duala, _⟩ :=
    farkas_dual (fun i j => (A i j : ℚ)) (fun _ => 0) w_Q 1 0 (by simp) hrec
  let B : ℚ := ∑ i : Fin k, u_dual i * (b i : ℚ)
  have hB_upper : ∀ x ∈ P, w_Q ⬝ᵥ x ≤ B := by
    intro x hxP
    rw [hP_eq] at hxP
    have hdot : w_Q ⬝ᵥ x = ∑ i : Fin k, u_dual i * ((fun j => (A i j : ℚ)) ⬝ᵥ x) := by
      rw [← hu_duala, sum_dotProduct]
      simp [smul_dotProduct]
    rw [hdot]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hxP i) (hu_dual0 i)
  -- Step 3: Project `{ (t, x) | x ∈ P ∧ t ≤ w_Q ⬝ᵥ x }` onto `t : ℚ` using `fm_proj`.
  let γ_sys : Option (Fin k) → ℚ := fun o => match o with
    | none => 1
    | some _ => 0
  let a_sys : Option (Fin k) → Fin n → ℚ := fun o => match o with
    | none => -w_Q
    | some i => fun j => (A i j : ℚ)
  let b_sys : Option (Fin k) → ℚ := fun o => match o with
    | none => 0
    | some i => (b i : ℚ)
  have hsys_iff : ∀ t : ℚ,
      (∃ x ∈ P, t ≤ w_Q ⬝ᵥ x) ↔ (∃ x : Fin n → ℚ, ∀ o, γ_sys o * t + a_sys o ⬝ᵥ x ≤ b_sys o) := by
    intro t
    simp only [hP_eq, Set.mem_setOf_eq]
    refine exists_congr fun x => ?_
    constructor
    · rintro ⟨hxA, hxt⟩ o
      cases o with
      | none =>
        simp only [γ_sys, a_sys, b_sys, one_mul, neg_dotProduct]
        linarith
      | some i =>
        simp only [γ_sys, a_sys, b_sys, zero_mul, zero_add]
        exact hxA i
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have hi := h (some i)
        simpa [γ_sys, a_sys, b_sys] using hi
      · have h0 := h none
        simp only [γ_sys, a_sys, b_sys, one_mul, neg_dotProduct] at h0
        linarith
  obtain ⟨κ, hκ, γ', b', hproj⟩ := fm_proj n γ_sys a_sys b_sys
  letI : Fintype κ := hκ
  have hproj' : ∀ t : ℚ, (∃ x ∈ P, t ≤ w_Q ⬝ᵥ x) ↔ (∀ j : κ, γ' j * t ≤ b' j) :=
    fun t => (hsys_iff t).trans (hproj t)
  let t0 : ℚ := w_Q ⬝ᵥ x0
  have ht0 : ∀ j : κ, γ' j * t0 ≤ b' j := (hproj' t0).mp ⟨x0, hx0P, le_rfl⟩
  let t1 : ℚ := max t0 B + 1
  have ht1_not : ¬ (∀ j : κ, γ' j * t1 ≤ b' j) := by
    intro h
    obtain ⟨x, hxP, htx⟩ := (hproj' t1).mpr h
    have hxB := hB_upper x hxP
    have : B < t1 := by dsimp only [t1]; linarith [le_max_right t0 B]
    linarith
  push_neg at ht1_not
  obtain ⟨j_pos, hj_pos_gt⟩ := ht1_not
  have hj_pos : 0 < γ' j_pos := by
    have h0 := ht0 j_pos
    have ht0_lt_t1 : t0 < t1 := by dsimp only [t1]; linarith [le_max_left t0 B]
    by_contra hle
    push_neg at hle
    nlinarith
  let Pos : Finset κ := Finset.univ.filter (fun j => 0 < γ' j)
  have hPos_ne : Pos.Nonempty := ⟨j_pos, by simp [Pos, hj_pos]⟩
  obtain ⟨j0, hj0_mem, hj0_min⟩ :=
    Finset.exists_min_image Pos (fun j => b' j / γ' j) hPos_ne
  have hj0_pos : 0 < γ' j0 := by simpa [Pos] using hj0_mem
  let μ : ℚ := b' j0 / γ' j0
  have ht0_le_μ : t0 ≤ μ := (le_div_iff₀ hj0_pos).mpr (by linarith [ht0 j0])
  have hμ_proj : ∀ j : κ, γ' j * μ ≤ b' j := by
    intro j
    by_cases hj : 0 < γ' j
    · have hmin : μ ≤ b' j / γ' j := hj0_min j (by simp [Pos, hj])
      have := (le_div_iff₀ hj).mp hmin
      linarith
    · push_neg at hj
      nlinarith [ht0 j]
  obtain ⟨xbar, hxbarP, hμ_le_xbar⟩ := (hproj' μ).mpr hμ_proj
  have h_upper : ∀ x ∈ P, w_Q ⬝ᵥ x ≤ μ := by
    intro x hxP
    have hx_proj := (hproj' (w_Q ⬝ᵥ x)).mp ⟨x, hxP, le_rfl⟩ j0
    exact (le_div_iff₀ hj0_pos).mpr (by linarith)
  have hxbar_eq : w_Q ⬝ᵥ xbar = μ := le_antisymm (h_upper xbar hxbarP) hμ_le_xbar
  refine ⟨μ, ⟨⟨xbar, hxbarP, hxbar_eq⟩, ?_⟩⟩
  rintro _ ⟨x, hxP, rfl⟩
  exact h_upper x hxP

/-! ### Section 7: Main Theorem (`chvatalIter_subset_halfspace`) -/

theorem solution {n : ℕ} (P : Set (Fin n → ℚ))
    (hP : IsPolyhedron P) (hPZ : ∃ x ∈ P, IsIntegral x)
    (w : Fin n → ℤ) (q : ℤ)
    (hq : IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' integerHull P) (q : ℚ)) :
    ∃ μ : ℚ, IsGreatest ((fun x => (fun i => (w i : ℚ)) ⬝ᵥ x) '' P) μ ∧
      chvatalIter ((n ^ (2 * n) * 2 ^ (n ^ 3) + 1) * (⌊μ⌋ - q).toNat + 1) P ⊆
        {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ (q : ℚ)} := by
  obtain ⟨μ, hμ_great⟩ := exists_lp_greatest P hP hPZ w q hq
  refine ⟨μ, hμ_great, ?_⟩
  set N := n ^ (2 * n) * 2 ^ (n ^ 3)
  set K := (⌊μ⌋ - q).toNat
  -- Show `q ≤ ⌊μ⌋` using an integral feasible point `x0 ∈ P`.
  have hq_le_floor : q ≤ ⌊μ⌋ := by
    obtain ⟨x0, hx0P, hx0I⟩ := hPZ
    -- Every point of `integerHull P` lies in `P` because `P` is convex.
    have hP_conv : Convex ℚ P := by
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
    have hhull_sub : integerHull P ⊆ P :=
      convexHull_min (fun z hz => hz.1) hP_conv
    rcases hq.1 with ⟨z, hz_hull, hzq⟩
    have hzμ : (fun i => (w i : ℚ)) ⬝ᵥ z ≤ μ := hμ_great.2 ⟨z, hhull_sub hz_hull, rfl⟩
    change (fun i => (w i : ℚ)) ⬝ᵥ z = (q : ℚ) at hzq
    rw [hzq] at hzμ
    exact Int.le_floor.mpr hzμ
  -- Induction over `j ≤ K` blocks of `N + 1` steps after the initial Chvátal closure.
  have hblock : ∀ j : ℕ, j ≤ K →
      IsPolyhedron (chvatalIter ((N + 1) * j + 1) P) ∧
      chvatalIter ((N + 1) * j + 1) P ⊆ P ∧
      chvatalIter ((N + 1) * j + 1) P ⊆
        {x | (fun i => (w i : ℚ)) ⬝ᵥ x ≤ ((⌊μ⌋ - (j : ℤ) : ℤ) : ℚ)} := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_zero, sub_zero]
      have h1_eq : chvatalIter 1 P = chvatalClosure P := rfl
      rw [h1_eq]
      refine ⟨isPolyhedron_chvatalClosure hP,
        chvatalClosure_subset_self_of_isPolyhedron hP, ?_⟩
      intro x hx
      exact hx w μ (fun y hy => hμ_great.2 ⟨y, hy, rfl⟩)
    | succ j ih =>
      intro hj_succ
      obtain ⟨hj_poly, hj_subP, hj_le⟩ := ih (Nat.le_of_succ_le hj_succ)
      have hq_lt_m : q < ⌊μ⌋ - (j : ℤ) := by
        dsimp only [K] at hj_succ
        omega
      have hiter_eq : chvatalIter ((N + 1) * (j + 1) + 1) P =
          chvatalIter (N + 1) (chvatalIter ((N + 1) * j + 1) P) := by
        rw [← chvatalIter_add]
        congr 1
        ring
      rw [hiter_eq]
      obtain ⟨h_poly', h_subP', h_le'⟩ :=
        chvatalIter_step_block hj_poly hj_subP w q (⌊μ⌋ - (j : ℤ)) hq hq_lt_m hj_le
      refine ⟨h_poly', h_subP', ?_⟩
      have hm_eq : (⌊μ⌋ - (j : ℤ) - 1 : ℤ) = ⌊μ⌋ - ((j + 1 : ℕ) : ℤ) := by omega
      rwa [hm_eq] at h_le'
  obtain ⟨_, _, hfinal⟩ := hblock K le_rfl
  have hK_eq : (⌊μ⌋ - (K : ℤ) : ℤ) = q := by
    dsimp only [K]
    omega
  rwa [hK_eq] at hfinal
