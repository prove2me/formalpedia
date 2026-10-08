-- Prove2me | solution 1 for BellmanDP.ExistUnique.type_three_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:45:48.425601+00:00
-- url     : https://prove2.me/submissions/e051c78b-0df4-4a33-8f69-5eee583ea68a

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree



namespace BellmanDP.ExistUnique

section T3

variable {n M : ℕ} {Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)} {c₁ : ℝ}

theorem t3_vertex_apply (k j : Fin (n + 1)) : vertex n k j = if j = k then 1 else 0 := by
  unfold vertex; rw [Pi.single_apply]

theorem t3_vertex_mem (k : Fin (n + 1)) : vertex n k ∈ simplex n := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [t3_vertex_apply]; split_ifs <;> norm_num
  · simp [t3_vertex_apply]

theorem t3_sum_vertex (k : Fin (n + 1)) (φ : (Fin (n + 1) → ℝ) → ℝ) :
    ∑ j, vertex n k j * φ (vertex n j) = φ (vertex n k) := by
  simp [t3_vertex_apply]

theorem t3_vertex_ne {k : Fin (n + 1)} (hk : k ≠ 0) : vertex n k ≠ vertex n 0 := by
  intro h
  have := congrFun h k
  rw [t3_vertex_apply, t3_vertex_apply, if_pos rfl, if_neg hk] at this
  norm_num at this

theorem t3_inf_le (hT : TypeThreeHyp n M Tr c₁) (φ : Fin M → ℝ) (l : Fin M) :
    ⨅ l, φ l ≤ φ l := ciInf_le (Set.finite_range _).bddBelow l

theorem t3_inf_attained (hT : TypeThreeHyp n M Tr c₁) (φ : Fin M → ℝ) :
    ∃ l, φ l = ⨅ l, φ l := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hT.M_pos⟩⟩
  exact exists_eq_ciInf_of_finite

/-- The chain lemma: follow the optimal continuation of `g` while it is not the stopping branch. -/
theorem t3_chain (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf : SolvesTypeThree n M Tr f) (hg : SolvesTypeThree n M Tr g)
    (B : ℝ) (hgB : ∀ p ∈ simplex n, -B ≤ g p) (p : Fin (n + 1) → ℝ) (hp : p ∈ simplex n) :
    ∃ q ∈ simplex n, f p - g p ≤ f q - g q ∧ (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) ∧
      (q = vertex n 0 ∨ g q = 1 + ∑ k, q k * g (vertex n k)) := by
  have main : ∀ m : ℕ, ∀ q ∈ simplex n, f p - g p ≤ f q - g q →
      (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) → g q < m - B →
      ∃ q ∈ simplex n, f p - g p ≤ f q - g q ∧ (q = p ∨ ∃ l r, r ∈ simplex n ∧ q = Tr l r) ∧
        (q = vertex n 0 ∨ g q = 1 + ∑ k, q k * g (vertex n k)) := by
    intro m
    induction m with
    | zero =>
      intro q hq _ _ hlt
      have := hgB q hq
      simp at hlt; linarith
    | succ m ih =>
      intro q hq hd hor hlt
      by_cases h0 : q = vertex n 0
      · exact ⟨q, hq, hd, hor, Or.inl h0⟩
      by_cases hA : g q = 1 + ∑ k, q k * g (vertex n k)
      · exact ⟨q, hq, hd, hor, Or.inr hA⟩
      have hgq := hg.2 q hq h0
      have hgq' : g q = ⨅ l, (1 + g (Tr l q)) := by
        rcases min_choice (1 + ∑ k, q k * g (vertex n k)) (⨅ l, (1 + g (Tr l q))) with h | h
        · exact absurd (hgq.trans h) hA
        · exact hgq.trans h
      obtain ⟨l, hl⟩ := t3_inf_attained hT (fun l => 1 + g (Tr l q))
      have hfq : f q ≤ 1 + f (Tr l q) := by
        rw [hf.2 q hq h0]
        exact (min_le_right _ _).trans (t3_inf_le hT (fun l => 1 + f (Tr l q)) l)
      have hgl : g q = 1 + g (Tr l q) := hgq'.trans hl.symm
      apply ih (Tr l q) (hT.mapsTo l q hq) (by linarith) (Or.inr ⟨l, q, hq, rfl⟩)
      push_cast at hlt; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (g p + B)
  exact main m p hp le_rfl (Or.inl rfl) (by linarith)

theorem t3_bound (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g)
    (p : Fin (n + 1) → ℝ) (hp : p ∈ simplex n) :
    f p - g p ≤ ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| := by
  set V := ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|
  have hV : ∀ k, |f (vertex n k) - g (vertex n k)| ≤ V := fun k =>
    le_ciSup (f := fun k : Fin (n + 1) => |f (vertex n k) - g (vertex n k)|) (Set.finite_range _).bddAbove k
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _) (hV 0)
  obtain ⟨B, hB⟩ := hg_bdd
  obtain ⟨q, hq, hd, -, hend⟩ := t3_chain hT f g hf hg B (fun p hp => by
    have := hB p hp; linarith [neg_abs_le (g p)]) p hp
  refine le_trans hd ?_
  rcases hend with h0 | hA
  · rw [h0, hf.1, hg.1]; simpa using hV0
  · have hne : q ≠ vertex n 0 := by
      intro h; subst h
      rw [hg.1, t3_sum_vertex, hg.1] at hA; norm_num at hA
    have hfq : f q ≤ 1 + ∑ k, q k * f (vertex n k) := by
      rw [hf.2 q hq hne]; exact min_le_left _ _
    have : ∑ k, q k * f (vertex n k) - ∑ k, q k * g (vertex n k) ≤ V := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ k, (q k * f (vertex n k) - q k * g (vertex n k)) ≤ ∑ k, q k * V := by
            apply Finset.sum_le_sum; intro k _
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hV k)) (hq.1 k)
        _ = V := by rw [← Finset.sum_mul, hq.2, one_mul]
    linarith

theorem t3_sup_core (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    IsLUB ((fun p => |f p - g p|) '' simplex n)
      (⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|) := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    have h1 := t3_bound hT f g hf_bdd hf hg_bdd hg p hp
    have h2 := t3_bound hT g f hg_bdd hg hf_bdd hf p hp
    have e : (⨆ k : Fin (n + 1), |g (vertex n k) - f (vertex n k)|)
        = ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| := by
      congr 1; ext k; exact abs_sub_comm _ _
    rw [e] at h2
    simp only
    rw [abs_le]; constructor <;> linarith
  · intro b hb
    apply ciSup_le
    intro k
    exact hb ⟨vertex n k, t3_vertex_mem k, rfl⟩


theorem t3_vert (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) (k : Fin (n + 1)) :
    f (vertex n k) - g (vertex n k) ≤ c₁ * ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| := by
  set V := ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|
  have hV : ∀ k, |f (vertex n k) - g (vertex n k)| ≤ V := fun k =>
    le_ciSup (f := fun k : Fin (n + 1) => |f (vertex n k) - g (vertex n k)|) (Set.finite_range _).bddAbove k
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _) (hV 0)
  have hcV : 0 ≤ c₁ * V := mul_nonneg hT.c_pos.le hV0
  by_cases hk : k = 0
  · subst hk; rw [hf.1, hg.1]; simpa using hcV
  obtain ⟨B, hB⟩ := hg_bdd
  obtain ⟨q, hq, hd, hor, hend⟩ := t3_chain hT f g hf hg B (fun p hp => by
    have := hB p hp; linarith [neg_abs_le (g p)]) (vertex n k) (t3_vertex_mem k)
  refine le_trans hd ?_
  rcases hor with hqk | ⟨l, r, hr, hqr⟩
  · exfalso
    subst hqk
    rcases hend with h0 | hA
    · exact t3_vertex_ne hk h0
    · rw [t3_sum_vertex] at hA; linarith
  rcases hend with h0 | hA
  · rw [h0, hf.1, hg.1]; simpa using hcV
  · have hne : q ≠ vertex n 0 := by
      intro h; subst h
      rw [hg.1, t3_sum_vertex, hg.1] at hA; norm_num at hA
    have hfq : f q ≤ 1 + ∑ k, q k * f (vertex n k) := by
      rw [hf.2 q hq hne]; exact min_le_left _ _
    have htail : ∑ j : Fin n, q j.succ ≤ c₁ := by rw [hqr]; exact hT.tail_le l r hr
    have : ∑ k, q k * f (vertex n k) - ∑ k, q k * g (vertex n k) ≤ c₁ * V := by
      rw [← Finset.sum_sub_distrib, Fin.sum_univ_succ, hf.1, hg.1]
      simp only [mul_zero, sub_zero, zero_add]
      calc ∑ j : Fin n, (q j.succ * f (vertex n j.succ) - q j.succ * g (vertex n j.succ))
            ≤ ∑ j : Fin n, q j.succ * V := by
            apply Finset.sum_le_sum; intro j _
            rw [← mul_sub]
            exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hV _)) (hq.1 _)
        _ = (∑ j : Fin n, q j.succ) * V := by rw [Finset.sum_mul]
        _ ≤ c₁ * V := mul_le_mul_of_nonneg_right htail hV0
    linarith

theorem t3_unique (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    ∀ p ∈ simplex n, g p = f p := by
  set V := ⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)| with hVdef
  have e : (⨆ k : Fin (n + 1), |g (vertex n k) - f (vertex n k)|) = V := by
    congr 1; ext k; exact abs_sub_comm _ _
  have hV0 : 0 ≤ V := le_trans (abs_nonneg _)
    (le_ciSup (f := fun k : Fin (n + 1) => |f (vertex n k) - g (vertex n k)|) (Set.finite_range _).bddAbove 0)
  have hVle : V ≤ c₁ * V := by
    apply ciSup_le; intro k
    have h1 := t3_vert hT f g hf_bdd hf hg_bdd hg k
    have h2 := t3_vert hT g f hg_bdd hg hf_bdd hf k
    rw [e] at h2
    rw [abs_le]; constructor <;> linarith
  have hV : V ≤ 0 := by nlinarith [hT.c_lt_one]
  intro p hp
  have := (t3_sup_core n M Tr c₁ hT f g hf_bdd hf hg_bdd hg).1 ⟨p, hp, rfl⟩
  have h3 : |f p - g p| ≤ 0 := le_trans this hV
  have := abs_nonpos_iff.mp h3
  linarith

open Classical in
/-- tail sum `Σ_{k ≥ 1} p_k` -/
noncomputable def t3s (p : Fin (n + 1) → ℝ) : ℝ := ∑ k : Fin n, p k.succ

theorem t3s_le_one {p : Fin (n + 1) → ℝ} (hp : p ∈ simplex n) : t3s p ≤ 1 := by
  have := hp.2; rw [Fin.sum_univ_succ] at this; unfold t3s; linarith [hp.1 0]

theorem t3s_nonneg {p : Fin (n + 1) → ℝ} (hp : p ∈ simplex n) : 0 ≤ t3s p :=
  Finset.sum_nonneg (fun k _ => hp.1 _)

open Classical in
noncomputable def t3U (n : ℕ) (α : ℝ) : (Fin (n + 1) → ℝ) → ℝ := fun p =>
  if p ∈ simplex n ∧ p ≠ vertex n 0 then α + α * t3s p else 0

open Classical in
noncomputable def t3Phi (n M : ℕ) (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ))
    (f : (Fin (n + 1) → ℝ) → ℝ) : (Fin (n + 1) → ℝ) → ℝ := fun p =>
  if p ∈ simplex n ∧ p ≠ vertex n 0 then
    min (1 + ∑ k, p k * f (vertex n k)) (⨅ l : Fin M, (1 + f (Tr l p))) else 0

theorem t3Phi_mono {f f' : (Fin (n + 1) → ℝ) → ℝ} (h : f ≤ f') : t3Phi n M Tr f ≤ t3Phi n M Tr f' := by
  intro p
  unfold t3Phi
  split_ifs with hp
  · apply min_le_min
    · apply add_le_add le_rfl
      apply Finset.sum_le_sum; intro k _
      exact mul_le_mul_of_nonneg_left (h _) (hp.1.1 k)
    · exact ciInf_mono (Set.finite_range _).bddBelow (fun l => add_le_add le_rfl (h _))
  · exact le_rfl

theorem t3Phi_ge (hT : TypeThreeHyp n M Tr c₁) {f : (Fin (n + 1) → ℝ) → ℝ} (h : 0 ≤ f)
    (p : Fin (n + 1) → ℝ) (hp : p ∈ simplex n ∧ p ≠ vertex n 0) : 1 ≤ t3Phi n M Tr f p := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hT.M_pos⟩⟩
  unfold t3Phi; rw [if_pos hp]
  apply le_min
  · have : 0 ≤ ∑ k, p k * f (vertex n k) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hp.1.1 k) (h _))
    linarith
  · apply le_ciInf; intro l
    have : (0:ℝ) ≤ f (Tr l p) := h (Tr l p)
    linarith

theorem t3Phi_nonneg (hT : TypeThreeHyp n M Tr c₁) {f : (Fin (n + 1) → ℝ) → ℝ} (h : 0 ≤ f) :
    0 ≤ t3Phi n M Tr f := by
  intro p
  by_cases hp : p ∈ simplex n ∧ p ≠ vertex n 0
  · exact le_trans zero_le_one (t3Phi_ge hT h p hp)
  · show 0 ≤ t3Phi n M Tr f p
    unfold t3Phi; rw [if_neg hp]

theorem t3U_nonneg {α : ℝ} (hα : 0 ≤ α) : (0 : (Fin (n + 1) → ℝ) → ℝ) ≤ t3U n α := by
  intro p; show 0 ≤ t3U n α p; unfold t3U; split_ifs with hp
  · exact add_nonneg hα (mul_nonneg hα (t3s_nonneg hp.1))
  · exact le_rfl

theorem t3U_le_two {α : ℝ} (hα : 0 ≤ α) (p : Fin (n + 1) → ℝ) : t3U n α p ≤ 2 * α := by
  unfold t3U; split_ifs with hp
  · have := t3s_le_one hp.1; nlinarith
  · linarith

theorem t3Phi_le_U (hT : TypeThreeHyp n M Tr c₁) {α : ℝ} (hα0 : 0 < α) (hα : α * (1 - c₁) = 2)
    {f : (Fin (n + 1) → ℝ) → ℝ} (h0 : 0 ≤ f) (hU : f ≤ t3U n α) :
    t3Phi n M Tr f ≤ t3U n α := by
  intro p
  show t3Phi n M Tr f p ≤ t3U n α p
  unfold t3Phi
  split_ifs with hp
  · have hUp : t3U n α p = α + α * t3s p := by unfold t3U; rw [if_pos hp]
    rw [hUp]
    by_cases hs : t3s p ≤ (1 + c₁) / 2
    · refine (min_le_left _ _).trans ?_
      have hx0 : f (vertex n 0) ≤ 0 := by
        have := hU (vertex n 0); unfold t3U at this
        rw [if_neg (fun (h : vertex n 0 ∈ simplex n ∧ vertex n 0 ≠ vertex n 0) => h.2 rfl)] at this; exact this
      rw [Fin.sum_univ_succ]
      have h1 : p 0 * f (vertex n 0) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hp.1.1 0) hx0
      have h2 : ∑ j : Fin n, p j.succ * f (vertex n j.succ) ≤ ∑ j : Fin n, p j.succ * (2 * α) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ((hU _).trans (t3U_le_two hα0.le _)) (hp.1.1 _))
      rw [← Finset.sum_mul] at h2
      change ∑ j : Fin n, p j.succ * f (vertex n j.succ) ≤ t3s p * (2 * α) at h2
      have h3 : α * t3s p ≤ α * ((1 + c₁) / 2) := mul_le_mul_of_nonneg_left hs hα0.le
      nlinarith
    · push_neg at hs
      have l : Fin M := ⟨0, hT.M_pos⟩
      refine (min_le_right _ _).trans ((t3_inf_le hT (fun l => 1 + f (Tr l p)) l).trans ?_)
      have hq := hT.mapsTo l p hp.1
      have hq0 : Tr l p ≠ vertex n 0 := by
        intro h; apply hT.zero_ne_one l p hp.1; rw [h, t3_vertex_apply, if_pos rfl]
      have hUq : f (Tr l p) ≤ α + α * t3s (Tr l p) := by
        have := hU (Tr l p); unfold t3U at this; rwa [if_pos ⟨hq, hq0⟩] at this
      have htail : t3s (Tr l p) ≤ c₁ := hT.tail_le l p hp.1
      have h3 : α * t3s (Tr l p) ≤ α * c₁ := mul_le_mul_of_nonneg_left htail hα0.le
      have h4 : α * ((1 + c₁) / 2) ≤ α * t3s p := mul_le_mul_of_nonneg_left hs.le hα0.le
      nlinarith
  · exact t3U_nonneg (n := n) hα0.le p

theorem t3_exists_core (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) :
    ∃ f : (Fin (n + 1) → ℝ) → ℝ,
      (BoundedOnSimplex n f ∧ SolvesTypeThree n M Tr f) ∧
      (∀ g : (Fin (n + 1) → ℝ) → ℝ, BoundedOnSimplex n g → SolvesTypeThree n M Tr g →
        ∀ p ∈ simplex n, g p = f p) ∧
      (∀ p ∈ simplex n, p ≠ vertex n 0 → 0 < f p) := by
  have hc := hT.c_lt_one
  set α : ℝ := 2 / (1 - c₁) with hαdef
  have hα0 : 0 < α := div_pos two_pos (by linarith)
  have hα : α * (1 - c₁) = 2 := by rw [hαdef]; field_simp [show (1 - c₁) ≠ 0 by linarith]
  haveI : Fact ((0 : (Fin (n + 1) → ℝ) → ℝ) ≤ t3U n α) := ⟨t3U_nonneg hα0.le⟩
  let Φ : Set.Icc (0 : (Fin (n + 1) → ℝ) → ℝ) (t3U n α) →o Set.Icc (0 : (Fin (n + 1) → ℝ) → ℝ) (t3U n α) :=
    { toFun := fun x => ⟨t3Phi n M Tr x.1, t3Phi_nonneg hT x.2.1, t3Phi_le_U hT hα0 hα x.2.1 x.2.2⟩
      monotone' := fun x y h => t3Phi_mono (Tr := Tr) (show x.1 ≤ y.1 from h) }
  have hfix : Φ (OrderHom.lfp Φ) = OrderHom.lfp Φ := Φ.map_lfp
  set F := OrderHom.lfp Φ with hFdef
  have hF : t3Phi n M Tr F.1 = F.1 := congrArg Subtype.val hfix
  have hsol : SolvesTypeThree n M Tr F.1 := by
    constructor
    · rw [← hF]; unfold t3Phi
      rw [if_neg (fun (h : vertex n 0 ∈ simplex n ∧ vertex n 0 ≠ vertex n 0) => h.2 rfl)]
    · intro p hp hne
      conv_lhs => rw [← hF]
      unfold t3Phi; rw [if_pos (show p ∈ simplex n ∧ p ≠ vertex n 0 from ⟨hp, hne⟩)]
  have hbdd : BoundedOnSimplex n F.1 := by
    refine ⟨2 * α, fun p _ => ?_⟩
    have h0 : 0 ≤ F.1 p := F.2.1 p
    have h1 : F.1 p ≤ t3U n α p := F.2.2 p
    rw [abs_of_nonneg h0]; exact h1.trans (t3U_le_two hα0.le p)
  refine ⟨F.1, ⟨hbdd, hsol⟩, fun g hg_bdd hg => t3_unique hT F.1 g hbdd hsol hg_bdd hg, ?_⟩
  intro p hp hne
  rw [← hF]
  exact lt_of_lt_of_le zero_lt_one (t3Phi_ge hT F.2.1 p ⟨hp, hne⟩)

end T3

end BellmanDP.ExistUnique

open BellmanDP.ExistUnique


theorem solution (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) :
    ∃ f : (Fin (n + 1) → ℝ) → ℝ,
      (BoundedOnSimplex n f ∧ SolvesTypeThree n M Tr f) ∧
      (∀ g : (Fin (n + 1) → ℝ) → ℝ, BoundedOnSimplex n g → SolvesTypeThree n M Tr g →
        ∀ p ∈ simplex n, g p = f p) ∧
      (∀ p ∈ simplex n, p ≠ vertex n 0 → 0 < f p) := by
  exact t3_exists_core n M Tr c₁ hT
