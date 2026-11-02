-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.lnat_convex_iff_submodular_integrally_convex
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-02T01:03:17.831199+00:00
-- url     : https://prove2.me/submissions/17960da8-33a6-4478-a19e-946b50f18f7e

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsIntegrallyConvexFunction

open Classical
open scoped Pointwise
open DiscreteConvex.LConvexFunctionsC

private abbrev V0 : Type := ULift.{0} Bool

private def uFalse : V0 := ULift.up false
private def uTrue : V0 := ULift.up true

private lemma uFalse_ne_uTrue : (uFalse : V0) ≠ uTrue := by
  intro h
  exact Bool.false_ne_true (ULift.up.inj h)

private lemma uTrue_ne_uFalse : (uTrue : V0) ≠ uFalse :=
  uFalse_ne_uTrue.symm

private noncomputable def gCounter (p : V0 → ℤ) : WithTop ℝ :=
  if p uFalse = 0 then ((p uTrue : ℝ) : WithTop ℝ)
  else if p uFalse = 2 then ((-(p uTrue : ℝ) : ℝ) : WithTop ℝ)
  else ⊤

private lemma gCounter_mem_domZ_iff (p : V0 → ℤ) :
    p ∈ DomZ gCounter ↔ p uFalse = 0 ∨ p uFalse = 2 := by
  unfold DomZ gCounter
  by_cases h0 : p uFalse = 0
  · simp [h0]
  · by_cases h2 : p uFalse = 2
    · simp [h0, h2]
    · simp [h0, h2]

private lemma gCounter_untopD_of_mem {p : V0 → ℤ} (hp : p ∈ DomZ gCounter) :
    (gCounter p).untopD 0 = (1 - (p uFalse : ℝ)) * (p uTrue : ℝ) := by
  rcases (gCounter_mem_domZ_iff p).mp hp with h0 | h2
  · unfold gCounter
    rw [if_pos h0, WithTop.untopD_coe, h0]
    ring
  · unfold gCounter
    have h0 : p uFalse ≠ 0 := by omega
    rw [if_neg h0, if_pos h2, WithTop.untopD_coe, h2]
    ring

private lemma gCounter_dom_nonempty : (DomZ (gCounter : (V0 → ℤ) → WithTop ℝ)).Nonempty := by
  refine ⟨0, ?_⟩
  rw [gCounter_mem_domZ_iff]
  left
  rfl

private lemma gCounter_not_lnat : ¬ LNaturalConvex (gCounter : (V0 → ℤ) → WithTop ℝ) := by
  rintro ⟨hSBF, _⟩
  let x1 : Option V0 → ℤ := fun o =>
    match o with
    | none => 0
    | some ⟨false⟩ => 2
    | some ⟨true⟩ => 0
  let x2 : Option V0 → ℤ := fun o =>
    match o with
    | none => 1
    | some ⟨false⟩ => 1
    | some ⟨true⟩ => 1
  have hineq := hSBF x1 x2
  unfold LiftedFunctionL at hineq
  have hx1 : gCounter (fun v => x1 (some v) - x1 none) = ((0 : ℝ) : WithTop ℝ) := by
    unfold gCounter uFalse uTrue
    rw [if_neg (by decide), if_pos (by decide)]
    norm_num [x1]
  have hx2 : gCounter (fun v => x2 (some v) - x2 none) = ((0 : ℝ) : WithTop ℝ) := by
    unfold gCounter uFalse uTrue
    rw [if_pos (by decide)]
    norm_num [x2]
  have hsup : gCounter (fun v => (x1 ⊔ x2) (some v) - (x1 ⊔ x2) none) = ⊤ := by
    unfold gCounter uFalse uTrue
    rw [if_neg (by decide), if_neg (by decide)]
  rw [hx1, hx2, hsup, top_add] at hineq
  have h00 : ((0 : ℝ) : WithTop ℝ) + ((0 : ℝ) : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) := by
    exact_mod_cast add_zero (0 : ℝ)
  rw [h00] at hineq
  exact WithTop.coe_ne_top (top_le_iff.mp hineq)

private lemma gCounter_sbf : SBF (gCounter : (V0 → ℤ) → WithTop ℝ) := by
  intro p q
  by_cases hp : p ∈ DomZ gCounter
  · by_cases hq : q ∈ DomZ gCounter
    · rcases (gCounter_mem_domZ_iff p).mp hp with hp0 | hp2 <;>
      rcases (gCounter_mem_domZ_iff q).mp hq with hq0 | hq2
      · have hsupF : (p ⊔ q) uFalse = 0 := by simp [Pi.sup_apply, hp0, hq0]
        have hinfF : (p ⊓ q) uFalse = 0 := by simp [Pi.inf_apply, hp0, hq0]
        unfold gCounter
        rw [if_pos hp0, if_pos hq0, if_pos hsupF, if_pos hinfF]
        change (((p ⊔ q) uTrue : ℝ) : WithTop ℝ) + (((p ⊓ q) uTrue : ℝ) : WithTop ℝ) ≤
          ((p uTrue : ℝ) : WithTop ℝ) + ((q uTrue : ℝ) : WithTop ℝ)
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        have hmm : (p ⊔ q) uTrue + (p ⊓ q) uTrue = p uTrue + q uTrue :=
          max_add_min (p uTrue) (q uTrue)
        exact_mod_cast hmm.le
      · have hsupF : (p ⊔ q) uFalse = 2 := by simp [Pi.sup_apply, hp0, hq2]
        have hsupF0 : (p ⊔ q) uFalse ≠ 0 := by omega
        have hinfF : (p ⊓ q) uFalse = 0 := by simp [Pi.inf_apply, hp0, hq2]
        have hq0 : q uFalse ≠ 0 := by omega
        unfold gCounter
        rw [if_pos hp0, if_neg hq0, if_pos hq2, if_neg hsupF0, if_pos hsupF, if_pos hinfF]
        change ((-((p ⊔ q) uTrue : ℝ) : ℝ) : WithTop ℝ) + (((p ⊓ q) uTrue : ℝ) : WithTop ℝ) ≤
          ((p uTrue : ℝ) : WithTop ℝ) + ((-(q uTrue : ℝ) : ℝ) : WithTop ℝ)
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        have h1 : (((p ⊓ q) uTrue : ℤ) : ℝ) ≤ (p uTrue : ℝ) := by
          exact_mod_cast min_le_left (p uTrue) (q uTrue)
        have h2 : (q uTrue : ℝ) ≤ (((p ⊔ q) uTrue : ℤ) : ℝ) := by
          exact_mod_cast le_max_right (p uTrue) (q uTrue)
        linarith
      · have hsupF : (p ⊔ q) uFalse = 2 := by simp [Pi.sup_apply, hp2, hq0]
        have hsupF0 : (p ⊔ q) uFalse ≠ 0 := by omega
        have hinfF : (p ⊓ q) uFalse = 0 := by simp [Pi.inf_apply, hp2, hq0]
        have hp0 : p uFalse ≠ 0 := by omega
        unfold gCounter
        rw [if_neg hp0, if_pos hp2, if_pos hq0, if_neg hsupF0, if_pos hsupF, if_pos hinfF]
        change ((-((p ⊔ q) uTrue : ℝ) : ℝ) : WithTop ℝ) + (((p ⊓ q) uTrue : ℝ) : WithTop ℝ) ≤
          ((-(p uTrue : ℝ) : ℝ) : WithTop ℝ) + ((q uTrue : ℝ) : WithTop ℝ)
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        have h1 : (((p ⊓ q) uTrue : ℤ) : ℝ) ≤ (q uTrue : ℝ) := by
          exact_mod_cast min_le_right (p uTrue) (q uTrue)
        have h2 : (p uTrue : ℝ) ≤ (((p ⊔ q) uTrue : ℤ) : ℝ) := by
          exact_mod_cast le_max_left (p uTrue) (q uTrue)
        linarith
      · have hsupF : (p ⊔ q) uFalse = 2 := by simp [Pi.sup_apply, hp2, hq2]
        have hsupF0 : (p ⊔ q) uFalse ≠ 0 := by omega
        have hinfF : (p ⊓ q) uFalse = 2 := by simp [Pi.inf_apply, hp2, hq2]
        have hinfF0 : (p ⊓ q) uFalse ≠ 0 := by omega
        have hp0 : p uFalse ≠ 0 := by omega
        have hq0 : q uFalse ≠ 0 := by omega
        unfold gCounter
        rw [if_neg hp0, if_pos hp2, if_neg hq0, if_pos hq2,
          if_neg hsupF0, if_pos hsupF, if_neg hinfF0, if_pos hinfF]
        change ((-((p ⊔ q) uTrue : ℝ) : ℝ) : WithTop ℝ) + ((-((p ⊓ q) uTrue : ℝ) : ℝ) : WithTop ℝ) ≤
          ((-(p uTrue : ℝ) : ℝ) : WithTop ℝ) + ((-(q uTrue : ℝ) : ℝ) : WithTop ℝ)
        rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
        have hmm : (p ⊔ q) uTrue + (p ⊓ q) uTrue = p uTrue + q uTrue :=
          max_add_min (p uTrue) (q uTrue)
        have hmmR : ((p ⊔ q) uTrue : ℝ) + ((p ⊓ q) uTrue : ℝ) = (p uTrue : ℝ) + (q uTrue : ℝ) := by
          exact_mod_cast hmm
        linarith
    · have hq_top : gCounter q = ⊤ := not_ne_iff.mp hq
      rw [hq_top, add_top]
      exact le_top
  · have hp_top : gCounter p = ⊤ := not_ne_iff.mp hp
    rw [hp_top, top_add]
    exact le_top

private lemma bddBelow_convexClosureValOn (g : (V0 → ℤ) → WithTop ℝ)
    (S : Finset (V0 → ℤ)) (x : V0 → ℝ) :
    BddBelow {L : WithTop ℝ | ∃ lam : (V0 → ℤ) → ℝ,
      (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ g) ∧
      (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
      L = ((∑ y ∈ S, lam y * (g y).untopD 0 : ℝ) : WithTop ℝ)} := by
  refine ⟨((∑ y ∈ S, -|(g y).untopD 0| : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨lam, h0, h1, _, _, rfl⟩
  rw [WithTop.coe_le_coe]
  apply Finset.sum_le_sum
  intro y hy
  have hlam0 : 0 ≤ lam y := h0 y hy
  have hlam1 : lam y ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum h0 hy
  have habs : -|(g y).untopD 0| ≤ (g y).untopD 0 := neg_abs_le ((g y).untopD 0)
  have habs0 : 0 ≤ |(g y).untopD 0| := abs_nonneg ((g y).untopD 0)
  nlinarith

private lemma sInf_eq_top_of_empty {S : Set (WithTop ℝ)} (h : S = ∅) : sInf S = ⊤ := by
  subst h
  change (if (∅ : Set (WithTop ℝ)) ⊆ {⊤} ∨ ¬BddBelow ∅ then ⊤ else _) = ⊤
  exact if_pos (Or.inl (Set.empty_subset _))

private lemma sInf_eq_top_of_subset_top {S : Set (WithTop ℝ)} (h : S ⊆ {⊤}) : sInf S = ⊤ := by
  change (if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else _) = ⊤
  exact if_pos (Or.inl h)

private lemma sInf_eq_top_of_not_bddBelow {S : Set (WithTop ℝ)} (h : ¬BddBelow S) : sInf S = ⊤ := by
  change (if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else _) = ⊤
  exact if_pos (Or.inr h)

private lemma gCounter_comb_bounds {S : Finset (V0 → ℤ)} {x : V0 → ℝ} {lam : (V0 → ℤ) → ℝ}
    (h0 : ∀ y ∈ S, 0 ≤ lam y) (h1 : ∑ y ∈ S, lam y = 1)
    (hdom : ∀ y ∈ S, y ∈ DomZ gCounter)
    (hx : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) :
    0 ≤ x uFalse ∧ x uFalse ≤ 2 ∧
      ∑ y ∈ S, lam y * (gCounter y).untopD 0 =
        ∑ y ∈ S, lam y * (1 - (y uFalse : ℝ)) * (y uTrue : ℝ) := by
  have hy_bounds : ∀ y ∈ S, 0 ≤ (y uFalse : ℝ) ∧ (y uFalse : ℝ) ≤ 2 := by
    intro y hy
    rcases (gCounter_mem_domZ_iff y).mp (hdom y hy) with hy0 | hy2 <;>
      constructor <;> norm_cast <;> omega
  refine ⟨?_, ?_, ?_⟩
  · rw [← hx uFalse]
    exact Finset.sum_nonneg (fun y hy => mul_nonneg (h0 y hy) (hy_bounds y hy).1)
  · rw [← hx uFalse]
    calc ∑ y ∈ S, lam y * (y uFalse : ℝ)
      _ ≤ ∑ y ∈ S, lam y * 2 :=
          Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hy_bounds y hy).2 (h0 y hy))
      _ = (∑ y ∈ S, lam y) * 2 := (Finset.sum_mul S lam 2).symm
      _ = 2 := by rw [h1]; ring
  · refine Finset.sum_congr rfl (fun y hy => ?_)
    rw [gCounter_untopD_of_mem (hdom y hy)]
    ring

private def mkPt (a b : ℤ) : V0 → ℤ :=
  fun v => if v = uFalse then a else b

@[simp] private lemma mkPt_uFalse (a b : ℤ) : mkPt a b uFalse = a := by
  simp [mkPt]

@[simp] private lemma mkPt_uTrue (a b : ℤ) : mkPt a b uTrue = b := by
  simp [mkPt, uTrue_ne_uFalse]

private lemma gCounter_val_le_of_k (x : V0 → ℝ) (ha_pos : 0 < x uFalse) (ha_lt2 : x uFalse < 2)
    (k : ℤ) :
    ∃ S : Finset (V0 → ℤ), (∀ y ∈ S, y ∈ DomZ gCounter) ∧
      ConvexClosureValOn gCounter S x ≤ ((x uTrue - x uFalse * (k : ℝ) : ℝ) : WithTop ℝ) := by
  let a := x uFalse
  let b := x uTrue
  let t := a / 2
  have ht0 : 0 < t := by dsimp [t, a]; linarith
  have ht1 : t < 1 := by dsimp [t, a]; linarith
  have h1t : 1 - t ≠ 0 := by linarith
  let z := (b - t * (k : ℝ)) / (1 - t)
  let n1 : ℤ := ⌊z⌋
  let n2 : ℤ := ⌊z⌋ + 1
  let alpha : ℝ := z - (n1 : ℝ)
  have halpha0 : 0 ≤ alpha := sub_nonneg.mpr (Int.floor_le z)
  have halpha1 : alpha ≤ 1 := by
    have hlt : z < (n1 : ℝ) + 1 := by
      dsimp only [n1]
      exact_mod_cast Int.lt_floor_add_one z
    dsimp only [alpha]
    linarith
  let p1 := mkPt 0 n1
  let p2 := mkPt 0 n2
  let p3 := mkPt 2 k
  let S : Finset (V0 → ℤ) := {p1, p2, p3}
  have hp12 : p1 ≠ p2 := by
    intro h; have := congr_fun h uTrue; simp [p1, p2, n1, n2] at this
  have hp13 : p1 ≠ p3 := by
    intro h; have := congr_fun h uFalse; simp [p1, p3] at this
  have hp23 : p2 ≠ p3 := by
    intro h; have := congr_fun h uFalse; simp [p2, p3] at this
  have hS_dom : ∀ y ∈ S, y ∈ DomZ gCounter := by
    intro y hy
    rw [gCounter_mem_domZ_iff]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · left; simp [p1]
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · left; simp [p2]
      · rw [Finset.mem_singleton.mp hy]; right; simp [p3]
  let lam : (V0 → ℤ) → ℝ := fun y =>
    if y = p1 then (1 - t) * (1 - alpha)
    else if y = p2 then (1 - t) * alpha
    else if y = p3 then t else 0
  have h0_lam : ∀ y ∈ S, 0 ≤ lam y := by
    intro y _
    dsimp only [lam]
    split_ifs <;> nlinarith
  have hsum_S : ∀ f : (V0 → ℤ) → ℝ,
      ∑ y ∈ S, f y = f p1 + f p2 + f p3 := by
    intro f
    dsimp [S]
    rw [Finset.sum_insert (by simp [hp12, hp13]),
      Finset.sum_pair hp23]
    ring
  have h1_lam : ∑ y ∈ S, lam y = 1 := by
    rw [hsum_S]
    dsimp only [lam]
    rw [if_pos rfl, if_neg (Ne.symm hp12), if_pos rfl,
      if_neg (Ne.symm hp13), if_neg (Ne.symm hp23), if_pos rfl]
    ring
  have hx_lam : ∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v := by
    intro ⟨v⟩
    rw [hsum_S]
    dsimp only [lam]
    rw [if_pos rfl, if_neg (Ne.symm hp12), if_pos rfl,
      if_neg (Ne.symm hp13), if_neg (Ne.symm hp23), if_pos rfl]
    cases v
    · change (1 - t) * (1 - alpha) * (p1 uFalse : ℝ) +
          (1 - t) * alpha * (p2 uFalse : ℝ) + t * (p3 uFalse : ℝ) = a
      simp only [p1, p2, p3, mkPt_uFalse, Int.cast_zero, Int.cast_ofNat]
      dsimp [t]
      ring
    · change (1 - t) * (1 - alpha) * (p1 uTrue : ℝ) +
          (1 - t) * alpha * (p2 uTrue : ℝ) + t * (p3 uTrue : ℝ) = b
      simp only [p1, p2, p3, mkPt_uTrue]
      have hn2 : (n2 : ℝ) = (n1 : ℝ) + 1 := by dsimp [n2, n1]; push_cast; ring
      rw [hn2]
      dsimp only [alpha, z]
      field_simp [h1t]
      ring
  have hval_lam : ∑ y ∈ S, lam y * (gCounter y).untopD 0 = b - a * (k : ℝ) := by
    rw [(gCounter_comb_bounds h0_lam h1_lam hS_dom hx_lam).2.2, hsum_S]
    dsimp only [lam]
    rw [if_pos rfl, if_neg (Ne.symm hp12), if_pos rfl,
      if_neg (Ne.symm hp13), if_neg (Ne.symm hp23), if_pos rfl]
    simp only [p1, p2, p3, mkPt_uFalse, mkPt_uTrue, Int.cast_zero, Int.cast_ofNat]
    have hn2 : (n2 : ℝ) = (n1 : ℝ) + 1 := by dsimp [n2, n1]; push_cast; ring
    have ha_eq : a = 2 * t := by dsimp [t]; ring
    rw [hn2, ha_eq]
    dsimp only [alpha, z]
    field_simp [h1t]
    ring
  refine ⟨S, hS_dom, ?_⟩
  rw [← hval_lam]
  exact csInf_le (bddBelow_convexClosureValOn gCounter S x)
    ⟨lam, h0_lam, h1_lam, hS_dom, hx_lam, rfl⟩

private lemma gCounter_ic : IsIntegrallyConvexFunction (gCounter : (V0 → ℤ) → WithTop ℝ) := by
  intro x
  let a := x uFalse
  let b := x uTrue
  let Sx := Finset.filter (fun y => y ∈ DomZ gCounter) (IntegralNeighborhoodFinset x)
  by_cases ha_out : a < 0 ∨ 2 < a
  · have h_empty_on : ∀ S : Finset (V0 → ℤ), ConvexClosureValOn gCounter S x = ⊤ := by
      intro S
      unfold ConvexClosureValOn
      apply sInf_eq_top_of_empty
      ext L
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro lam h0 h1 hdom hx _
      have hbnd := gCounter_comb_bounds h0 h1 hdom hx
      rcases ha_out with ha0 | ha2 <;> linarith [hbnd.1, hbnd.2.1]
    rw [h_empty_on Sx]
    unfold ConvexClosureVal
    apply sInf_eq_top_of_subset_top
    rintro L ⟨S, _, rfl⟩
    simp [h_empty_on S]
  · have ha0 : 0 ≤ a := by
      by_contra h; exact ha_out (Or.inl (not_le.mp h))
    have ha2 : a ≤ 2 := by
      by_contra h; exact ha_out (Or.inr (not_le.mp h))
    by_cases ha_eq0 : a = 0
    · have h_val_eq : ∀ (S : Finset (V0 → ℤ)) (lam : (V0 → ℤ) → ℝ),
          (∀ y ∈ S, 0 ≤ lam y) → (∑ y ∈ S, lam y = 1) →
          (∀ y ∈ S, y ∈ DomZ gCounter) → (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) →
          ∑ y ∈ S, lam y * (gCounter y).untopD 0 = b := by
        intro S lam h0 h1 hdom hx
        have hsumF : ∑ y ∈ S, lam y * (y uFalse : ℝ) = 0 := by
          rw [hx uFalse]; exact ha_eq0
        have hterm0 : ∀ y ∈ S, lam y * (y uFalse : ℝ) = 0 := by
          have hnonneg : ∀ y ∈ S, 0 ≤ lam y * (y uFalse : ℝ) := by
            intro y hy
            apply mul_nonneg (h0 y hy)
            rcases (gCounter_mem_domZ_iff y).mp (hdom y hy) with hy0 | hy2 <;>
              norm_cast <;> omega
          exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumF
        calc ∑ y ∈ S, lam y * (gCounter y).untopD 0
          _ = ∑ y ∈ S, lam y * (1 - (y uFalse : ℝ)) * (y uTrue : ℝ) :=
              (gCounter_comb_bounds h0 h1 hdom hx).2.2
          _ = ∑ y ∈ S, lam y * (y uTrue : ℝ) := by
              refine Finset.sum_congr rfl (fun y hy => ?_)
              calc lam y * (1 - (y uFalse : ℝ)) * (y uTrue : ℝ)
                _ = (lam y - lam y * (y uFalse : ℝ)) * (y uTrue : ℝ) := by ring
                _ = lam y * (y uTrue : ℝ) := by rw [hterm0 y hy]; ring
          _ = b := hx uTrue
      let y1 := mkPt 0 ⌊b⌋
      let y2 := mkPt 0 ⌈b⌉
      have hy1_Sx : y1 ∈ Sx := by
        simp only [Sx, Finset.mem_filter, IntegralNeighborhoodFinset, Fintype.mem_piFinset,
          Finset.mem_Icc]
        refine ⟨fun ⟨v⟩ => ?_, (gCounter_mem_domZ_iff y1).mpr (Or.inl (by simp [y1]))⟩
        cases v
        · change ⌊a⌋ ≤ y1 uFalse ∧ y1 uFalse ≤ ⌈a⌉
          simp [y1, ha_eq0]
        · change ⌊b⌋ ≤ y1 uTrue ∧ y1 uTrue ≤ ⌈b⌉
          simp [y1]
          exact Int.floor_le_ceil b
      have hy2_Sx : y2 ∈ Sx := by
        simp only [Sx, Finset.mem_filter, IntegralNeighborhoodFinset, Fintype.mem_piFinset,
          Finset.mem_Icc]
        refine ⟨fun ⟨v⟩ => ?_, (gCounter_mem_domZ_iff y2).mpr (Or.inl (by simp [y2]))⟩
        cases v
        · change ⌊a⌋ ≤ y2 uFalse ∧ y2 uFalse ≤ ⌈a⌉
          simp [y2, ha_eq0]
        · change ⌊b⌋ ≤ y2 uTrue ∧ y2 uTrue ≤ ⌈b⌉
          simp [y2]
          exact Int.floor_le_ceil b
      have hSx_val : ConvexClosureValOn gCounter Sx x = ((b : ℝ) : WithTop ℝ) := by
        unfold ConvexClosureValOn
        apply IsLeast.csInf_eq
        constructor
        · by_cases hy12 : y1 = y2
          · have hb_eq : (⌊b⌋ : ℝ) = b := by
              have hfl_ce : ⌊b⌋ = ⌈b⌉ := by
                have := congr_fun hy12 uTrue
                simpa [y1, y2] using this
              have h1 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
              have h2 : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
              rw [← hfl_ce] at h2
              linarith
            have h0 : ∀ y ∈ Sx, 0 ≤ (if y = y1 then (1 : ℝ) else 0) := by
              intro y _; split_ifs <;> linarith
            have h1 : ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) = 1 := by
              simp [hy1_Sx]
            have hdom : ∀ y ∈ Sx, y ∈ DomZ gCounter := fun y hy => (Finset.mem_filter.mp hy).2
            have hx_eq : ∀ v, ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y v : ℝ) = x v := by
              intro ⟨v⟩; cases v
              · change ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y uFalse : ℝ) = a
                simp [hy1_Sx, y1, ha_eq0]
              · change ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y uTrue : ℝ) = b
                simp [hy1_Sx, y1, hb_eq]
            refine ⟨fun y => if y = y1 then 1 else 0, h0, h1, hdom, hx_eq, ?_⟩
            rw [h_val_eq Sx _ h0 h1 hdom hx_eq]
          · have hce_eq : ⌈b⌉ = ⌊b⌋ + 1 := by
              have hlt : b ≤ ((⌊b⌋ + 1 : ℤ) : ℝ) := by
                push_cast
                exact (Int.lt_floor_add_one b).le
              have hle1 : ⌈b⌉ ≤ ⌊b⌋ + 1 := Int.ceil_le.mpr hlt
              have hle2 : ⌊b⌋ ≤ ⌈b⌉ := Int.floor_le_ceil b
              have hne : ⌊b⌋ ≠ ⌈b⌉ := by
                intro h
                apply hy12
                ext ⟨v⟩; cases v <;> simp [y1, y2, h]
              omega
            let alpha := b - (⌊b⌋ : ℝ)
            have halpha0 : 0 ≤ alpha := sub_nonneg.mpr (Int.floor_le b)
            have halpha1 : alpha ≤ 1 := by
              have hlt : b < (⌊b⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one b
              dsimp only [alpha]
              linarith
            let lam : (V0 → ℤ) → ℝ := fun y =>
              if y = y1 then 1 - alpha else if y = y2 then alpha else 0
            have h0 : ∀ y ∈ Sx, 0 ≤ lam y := by
              intro y _
              dsimp only [lam]
              split_ifs <;> linarith
            have h1 : ∑ y ∈ Sx, lam y = 1 := by
              have hsub : ({y1, y2} : Finset (V0 → ℤ)) ⊆ Sx := by
                intro y hy
                rcases Finset.mem_insert.mp hy with rfl | hy
                · exact hy1_Sx
                · rw [Finset.mem_singleton.mp hy]; exact hy2_Sx
              rw [← Finset.sum_subset hsub]
              · rw [Finset.sum_pair hy12]
                dsimp only [lam]
                rw [if_pos rfl, if_neg (Ne.symm hy12), if_pos rfl]
                ring
              · intro y _ hy_not
                dsimp only [lam]
                have h1' : y ≠ y1 := fun h => hy_not (by simp [h])
                have h2' : y ≠ y2 := fun h => hy_not (by simp [h])
                rw [if_neg h1', if_neg h2']
            have hdom : ∀ y ∈ Sx, y ∈ DomZ gCounter := fun y hy => (Finset.mem_filter.mp hy).2
            have hx_eq : ∀ v, ∑ y ∈ Sx, lam y * (y v : ℝ) = x v := by
              intro ⟨v⟩
              have hsub : ({y1, y2} : Finset (V0 → ℤ)) ⊆ Sx := by
                intro y hy
                rcases Finset.mem_insert.mp hy with rfl | hy
                · exact hy1_Sx
                · rw [Finset.mem_singleton.mp hy]; exact hy2_Sx
              rw [← Finset.sum_subset hsub]
              · rw [Finset.sum_pair hy12]
                cases v
                · change lam y1 * (y1 uFalse : ℝ) + lam y2 * (y2 uFalse : ℝ) = a
                  simp [y1, y2, ha_eq0]
                · change lam y1 * (y1 uTrue : ℝ) + lam y2 * (y2 uTrue : ℝ) = b
                  dsimp only [lam]
                  rw [if_pos rfl, if_neg (Ne.symm hy12), if_pos rfl]
                  simp only [y1, y2, mkPt_uTrue, hce_eq, Int.cast_add, Int.cast_one]
                  dsimp only [alpha]
                  ring
              · intro y _ hy_not
                dsimp only [lam]
                have h1' : y ≠ y1 := fun h => hy_not (by simp [h])
                have h2' : y ≠ y2 := fun h => hy_not (by simp [h])
                rw [if_neg h1', if_neg h2', zero_mul]
            refine ⟨lam, h0, h1, hdom, hx_eq, ?_⟩
            rw [h_val_eq Sx lam h0 h1 hdom hx_eq]
        · rintro L ⟨lam, h0, h1, hdom, hx_eq, rfl⟩
          rw [h_val_eq Sx lam h0 h1 hdom hx_eq]
      rw [hSx_val]
      unfold ConvexClosureVal
      apply IsLeast.csInf_eq
      constructor
      · refine ⟨Sx, fun y hy => (Finset.mem_filter.mp hy).2, hSx_val.symm⟩
      · rintro L ⟨S, _, rfl⟩
        unfold ConvexClosureValOn
        rcases Set.eq_empty_or_nonempty {L : WithTop ℝ | ∃ lam : (V0 → ℤ) → ℝ,
            (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ gCounter) ∧
            (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
            L = ((∑ y ∈ S, lam y * (gCounter y).untopD 0 : ℝ) : WithTop ℝ)} with he | hne
        · rw [sInf_eq_top_of_empty he]; exact le_top
        · apply le_csInf hne
          rintro L' ⟨lam, h0, h1, hdom, hx_eq, rfl⟩
          rw [h_val_eq S lam h0 h1 hdom hx_eq]
    · by_cases ha_eq2 : a = 2
      · have h_val_eq : ∀ (S : Finset (V0 → ℤ)) (lam : (V0 → ℤ) → ℝ),
            (∀ y ∈ S, 0 ≤ lam y) → (∑ y ∈ S, lam y = 1) →
            (∀ y ∈ S, y ∈ DomZ gCounter) → (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) →
            ∑ y ∈ S, lam y * (gCounter y).untopD 0 = -b := by
          intro S lam h0 h1 hdom hx
          have hsumF : ∑ y ∈ S, lam y * (2 - (y uFalse : ℝ)) = 0 := by
            have : ∑ y ∈ S, lam y * (2 - (y uFalse : ℝ)) =
                (∑ y ∈ S, lam y) * 2 - ∑ y ∈ S, lam y * (y uFalse : ℝ) := by
              rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl (fun y _ => by ring)
            rw [this, h1, hx uFalse]
            change 1 * 2 - a = 0
            rw [ha_eq2]
            ring
          have hterm0 : ∀ y ∈ S, lam y * (2 - (y uFalse : ℝ)) = 0 := by
            have hnonneg : ∀ y ∈ S, 0 ≤ lam y * (2 - (y uFalse : ℝ)) := by
              intro y hy
              apply mul_nonneg (h0 y hy)
              have hbnd := (gCounter_mem_domZ_iff y).mp (hdom y hy)
              rcases hbnd with hy0 | hy2 <;> norm_cast <;> omega
            exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsumF
          calc ∑ y ∈ S, lam y * (gCounter y).untopD 0
            _ = ∑ y ∈ S, lam y * (1 - (y uFalse : ℝ)) * (y uTrue : ℝ) :=
                (gCounter_comb_bounds h0 h1 hdom hx).2.2
            _ = ∑ y ∈ S, -(lam y * (y uTrue : ℝ)) := by
                refine Finset.sum_congr rfl (fun y hy => ?_)
                calc lam y * (1 - (y uFalse : ℝ)) * (y uTrue : ℝ)
                  _ = (lam y * (2 - (y uFalse : ℝ)) - lam y) * (y uTrue : ℝ) := by ring
                  _ = -(lam y * (y uTrue : ℝ)) := by rw [hterm0 y hy]; ring
            _ = -b := by rw [Finset.sum_neg_distrib, hx uTrue]
        let y1 := mkPt 2 ⌊b⌋
        let y2 := mkPt 2 ⌈b⌉
        have hy1_Sx : y1 ∈ Sx := by
          simp only [Sx, Finset.mem_filter, IntegralNeighborhoodFinset, Fintype.mem_piFinset,
            Finset.mem_Icc]
          refine ⟨fun ⟨v⟩ => ?_, (gCounter_mem_domZ_iff y1).mpr (Or.inr (by simp [y1]))⟩
          cases v
          · change ⌊a⌋ ≤ y1 uFalse ∧ y1 uFalse ≤ ⌈a⌉
            simp [y1, ha_eq2]
          · change ⌊b⌋ ≤ y1 uTrue ∧ y1 uTrue ≤ ⌈b⌉
            simp [y1]
            exact Int.floor_le_ceil b
        have hy2_Sx : y2 ∈ Sx := by
          simp only [Sx, Finset.mem_filter, IntegralNeighborhoodFinset, Fintype.mem_piFinset,
            Finset.mem_Icc]
          refine ⟨fun ⟨v⟩ => ?_, (gCounter_mem_domZ_iff y2).mpr (Or.inr (by simp [y2]))⟩
          cases v
          · change ⌊a⌋ ≤ y2 uFalse ∧ y2 uFalse ≤ ⌈a⌉
            simp [y2, ha_eq2]
          · change ⌊b⌋ ≤ y2 uTrue ∧ y2 uTrue ≤ ⌈b⌉
            simp [y2]
            exact Int.floor_le_ceil b
        have hSx_val : ConvexClosureValOn gCounter Sx x = ((-b : ℝ) : WithTop ℝ) := by
          unfold ConvexClosureValOn
          apply IsLeast.csInf_eq
          constructor
          · by_cases hy12 : y1 = y2
            · have hb_eq : (⌊b⌋ : ℝ) = b := by
                have hfl_ce : ⌊b⌋ = ⌈b⌉ := by
                  have := congr_fun hy12 uTrue
                  simpa [y1, y2] using this
                have h1 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
                have h2 : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
                rw [← hfl_ce] at h2
                linarith
              have h0 : ∀ y ∈ Sx, 0 ≤ (if y = y1 then (1 : ℝ) else 0) := by
                intro y _; split_ifs <;> linarith
              have h1 : ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) = 1 := by
                simp [hy1_Sx]
              have hdom : ∀ y ∈ Sx, y ∈ DomZ gCounter := fun y hy => (Finset.mem_filter.mp hy).2
              have hx_eq : ∀ v, ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y v : ℝ) = x v := by
                intro ⟨v⟩; cases v
                · change ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y uFalse : ℝ) = a
                  simp [hy1_Sx, y1, ha_eq2]
                · change ∑ y ∈ Sx, (if y = y1 then (1 : ℝ) else 0) * (y uTrue : ℝ) = b
                  simp [hy1_Sx, y1, hb_eq]
              refine ⟨fun y => if y = y1 then 1 else 0, h0, h1, hdom, hx_eq, ?_⟩
              rw [h_val_eq Sx _ h0 h1 hdom hx_eq]
            · have hce_eq : ⌈b⌉ = ⌊b⌋ + 1 := by
                have hlt : b ≤ ((⌊b⌋ + 1 : ℤ) : ℝ) := by
                  push_cast
                  exact (Int.lt_floor_add_one b).le
                have hle1 : ⌈b⌉ ≤ ⌊b⌋ + 1 := Int.ceil_le.mpr hlt
                have hle2 : ⌊b⌋ ≤ ⌈b⌉ := Int.floor_le_ceil b
                have hne : ⌊b⌋ ≠ ⌈b⌉ := by
                  intro h
                  apply hy12
                  ext ⟨v⟩; cases v <;> simp [y1, y2, h]
                omega
              let alpha := b - (⌊b⌋ : ℝ)
              have halpha0 : 0 ≤ alpha := sub_nonneg.mpr (Int.floor_le b)
              have halpha1 : alpha ≤ 1 := by
                have hlt : b < (⌊b⌋ : ℝ) + 1 := by exact_mod_cast Int.lt_floor_add_one b
                dsimp only [alpha]
                linarith
              let lam : (V0 → ℤ) → ℝ := fun y =>
                if y = y1 then 1 - alpha else if y = y2 then alpha else 0
              have h0 : ∀ y ∈ Sx, 0 ≤ lam y := by
                intro y _
                dsimp only [lam]
                split_ifs <;> linarith
              have h1 : ∑ y ∈ Sx, lam y = 1 := by
                have hsub : ({y1, y2} : Finset (V0 → ℤ)) ⊆ Sx := by
                  intro y hy
                  rcases Finset.mem_insert.mp hy with rfl | hy
                  · exact hy1_Sx
                  · rw [Finset.mem_singleton.mp hy]; exact hy2_Sx
                rw [← Finset.sum_subset hsub]
                · rw [Finset.sum_pair hy12]
                  dsimp only [lam]
                  rw [if_pos rfl, if_neg (Ne.symm hy12), if_pos rfl]
                  ring
                · intro y _ hy_not
                  dsimp only [lam]
                  have h1' : y ≠ y1 := fun h => hy_not (by simp [h])
                  have h2' : y ≠ y2 := fun h => hy_not (by simp [h])
                  rw [if_neg h1', if_neg h2']
              have hdom : ∀ y ∈ Sx, y ∈ DomZ gCounter := fun y hy => (Finset.mem_filter.mp hy).2
              have hx_eq : ∀ v, ∑ y ∈ Sx, lam y * (y v : ℝ) = x v := by
                intro ⟨v⟩
                have hsub : ({y1, y2} : Finset (V0 → ℤ)) ⊆ Sx := by
                  intro y hy
                  rcases Finset.mem_insert.mp hy with rfl | hy
                  · exact hy1_Sx
                  · rw [Finset.mem_singleton.mp hy]; exact hy2_Sx
                rw [← Finset.sum_subset hsub]
                · rw [Finset.sum_pair hy12]
                  cases v
                  · change lam y1 * (y1 uFalse : ℝ) + lam y2 * (y2 uFalse : ℝ) = a
                    dsimp only [lam]
                    rw [if_pos rfl, if_neg (Ne.symm hy12), if_pos rfl]
                    simp only [y1, y2, mkPt_uFalse, Int.cast_ofNat, ha_eq2]
                    ring
                  · change lam y1 * (y1 uTrue : ℝ) + lam y2 * (y2 uTrue : ℝ) = b
                    dsimp only [lam]
                    rw [if_pos rfl, if_neg (Ne.symm hy12), if_pos rfl]
                    simp only [y1, y2, mkPt_uTrue, hce_eq, Int.cast_add, Int.cast_one]
                    dsimp only [alpha]
                    ring
                · intro y _ hy_not
                  dsimp only [lam]
                  have h1' : y ≠ y1 := fun h => hy_not (by simp [h])
                  have h2' : y ≠ y2 := fun h => hy_not (by simp [h])
                  rw [if_neg h1', if_neg h2', zero_mul]
              refine ⟨lam, h0, h1, hdom, hx_eq, ?_⟩
              rw [h_val_eq Sx lam h0 h1 hdom hx_eq]
          · rintro L ⟨lam, h0, h1, hdom, hx_eq, rfl⟩
            rw [h_val_eq Sx lam h0 h1 hdom hx_eq]
        rw [hSx_val]
        unfold ConvexClosureVal
        apply IsLeast.csInf_eq
        constructor
        · refine ⟨Sx, fun y hy => (Finset.mem_filter.mp hy).2, hSx_val.symm⟩
        · rintro L ⟨S, _, rfl⟩
          unfold ConvexClosureValOn
          rcases Set.eq_empty_or_nonempty {L : WithTop ℝ | ∃ lam : (V0 → ℤ) → ℝ,
              (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ gCounter) ∧
              (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
              L = ((∑ y ∈ S, lam y * (gCounter y).untopD 0 : ℝ) : WithTop ℝ)} with he | hne
          · rw [sInf_eq_top_of_empty he]; exact le_top
          · apply le_csInf hne
            rintro L' ⟨lam, h0, h1, hdom, hx_eq, rfl⟩
            rw [h_val_eq S lam h0 h1 hdom hx_eq]
      · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha_eq0)
        have ha_lt2 : a < 2 := lt_of_le_of_ne ha2 ha_eq2
        have hSx_top : ConvexClosureValOn gCounter Sx x = ⊤ := by
          unfold ConvexClosureValOn
          apply sInf_eq_top_of_empty
          ext L
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
          intro lam h0 h1 _ hx_eq _
          by_cases ha_le1 : a ≤ 1
          · have hce : ⌈a⌉ ≤ 1 := Int.ceil_le.mpr (by exact_mod_cast ha_le1)
            have hyF0 : ∀ y ∈ Sx, (y uFalse : ℝ) = 0 := by
              intro y hy
              rcases Finset.mem_filter.mp hy with ⟨hyN, hyD⟩
              have hyIcc := (Fintype.mem_piFinset.mp hyN) uFalse
              rw [Finset.mem_Icc] at hyIcc
              have h1' : y uFalse ≤ ⌈a⌉ := hyIcc.2
              rcases (gCounter_mem_domZ_iff y).mp hyD with hy0 | hy2
              · exact_mod_cast hy0
              · omega
            have hsum0 : ∑ y ∈ Sx, lam y * (y uFalse : ℝ) = 0 :=
              Finset.sum_eq_zero (fun y hy => by rw [hyF0 y hy, mul_zero])
            linarith [hx_eq uFalse]
          · have ha_gt1 : 1 < a := not_le.mp ha_le1
            have hfl : 1 ≤ ⌊a⌋ := Int.le_floor.mpr (by exact_mod_cast ha_gt1.le)
            have hyF2 : ∀ y ∈ Sx, (y uFalse : ℝ) = 2 := by
              intro y hy
              rcases Finset.mem_filter.mp hy with ⟨hyN, hyD⟩
              have hyIcc := (Fintype.mem_piFinset.mp hyN) uFalse
              rw [Finset.mem_Icc] at hyIcc
              have h1' : ⌊a⌋ ≤ y uFalse := hyIcc.1
              rcases (gCounter_mem_domZ_iff y).mp hyD with hy0 | hy2
              · omega
              · exact_mod_cast hy2
            have hsum2 : ∑ y ∈ Sx, lam y * (y uFalse : ℝ) = 2 := by
              calc ∑ y ∈ Sx, lam y * (y uFalse : ℝ)
                _ = ∑ y ∈ Sx, lam y * 2 :=
                    Finset.sum_congr rfl (fun y hy => by rw [hyF2 y hy])
                _ = (∑ y ∈ Sx, lam y) * 2 := (Finset.sum_mul Sx lam 2).symm
                _ = 2 := by rw [h1]; ring
            linarith [hx_eq uFalse]
        rw [hSx_top]
        unfold ConvexClosureVal
        apply sInf_eq_top_of_not_bddBelow
        rintro ⟨B, hB⟩
        cases B with
        | top =>
          obtain ⟨S, hS_dom, h_on_le⟩ := gCounter_val_le_of_k x ha_pos ha_lt2 0
          have htop_le := (hB ⟨S, hS_dom, rfl⟩).trans h_on_le
          exact WithTop.coe_ne_top (top_le_iff.mp htop_le)
        | coe B =>
          let k : ℤ := ⌈(b - B + 1) / a⌉
          have hk : (b - B + 1) / a ≤ (k : ℝ) := Int.le_ceil _
          have hk_lt : b - a * (k : ℝ) < B := by
            have := (div_le_iff₀ ha_pos).mp hk
            linarith
          obtain ⟨S, hS_dom, h_on_le⟩ := gCounter_val_le_of_k x ha_pos ha_lt2 k
          have hB_le := (hB ⟨S, hS_dom, rfl⟩).trans h_on_le
          rw [WithTop.coe_le_coe] at hB_le
          linarith

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ)
      (_hdom : (DomZ g).Nonempty),
      LNaturalConvex g ↔ (SBF g ∧ IsIntegrallyConvexFunction g)) := by
  intro h
  have hiff := h (V := V0) gCounter gCounter_dom_nonempty
  exact gCounter_not_lnat (hiff.mpr ⟨gCounter_sbf, gCounter_ic⟩)
