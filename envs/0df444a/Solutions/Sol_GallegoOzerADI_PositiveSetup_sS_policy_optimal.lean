-- Prove2me | solution 1 for GallegoOzerADI.PositiveSetup.sS_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:40:59.297702+00:00
-- url     : https://prove2.me/submissions/4cf5d748-7666-4a88-8948-82fb2b48dae7

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup

def aux_so_KC (K : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    f (θ * x₁ + (1 - θ) * x₂) ≤ θ * f x₁ + (1 - θ) * (K + f x₂)

lemma aux_so_KC_three {K : ℝ} {f : ℝ → ℝ} (hf : aux_so_KC K f) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hac : a < c) :
    (c - a) * f b ≤ (c - b) * f a + (b - a) * (K + f c) := by
  have hca : 0 < c - a := by linarith
  set θ := (c - b) / (c - a) with hθ
  have h0 : 0 ≤ θ := div_nonneg (by linarith) hca.le
  have h1 : θ ≤ 1 := (div_le_one hca).2 (by linarith)
  have e1 : (c - a) * θ = c - b := by rw [hθ]; field_simp
  have e2 : (c - a) * (1 - θ) = b - a := by rw [mul_sub, e1]; ring
  have hb : θ * a + (1 - θ) * c = b := by
    have : (c - a) * (θ * a + (1 - θ) * c) = (c - a) * b := by
      have : (c - a) * (θ * a + (1 - θ) * c) = ((c - a) * θ) * a + ((c - a) * (1 - θ)) * c := by
        ring
      rw [this, e1, e2]; ring
    exact mul_left_cancel₀ hca.ne' this
  have := hf a c hac.le θ h0 h1
  rw [hb] at this
  calc (c - a) * f b ≤ (c - a) * (θ * f a + (1 - θ) * (K + f c)) :=
        mul_le_mul_of_nonneg_left this hca.le
    _ = ((c - a) * θ) * f a + ((c - a) * (1 - θ)) * (K + f c) := by ring
    _ = (c - b) * f a + (b - a) * (K + f c) := by rw [e1, e2]

lemma aux_so_min_attained {f : ℝ → ℝ} (hc : Continuous f)
    (hco : Tendsto f (cocompact ℝ) atTop) (x : ℝ) :
    ∃ y, x ≤ y ∧ ∀ z, x ≤ z → f y ≤ f z := by
  obtain ⟨y, hy, hmin⟩ := hc.continuousOn.exists_isMinOn' (s := Set.Ici x) isClosed_Ici
    Set.self_mem_Ici (((hco.eventually (eventually_ge_atTop (f x)))).filter_mono inf_le_left)
  exact ⟨y, hy, fun z hz => hmin hz⟩

lemma aux_so_scarf {K : ℝ} (hK : 0 < K) {f : ℝ → ℝ} (hc : Continuous f)
    (hkc : aux_so_KC K f) (hco : Tendsto f (cocompact ℝ) atTop) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, f y ≤ f x} S ∧ IsGreatest {x | reorderGap K f x ≤ 0} s ∧
      s < S ∧ f s = K + f S ∧ (∀ x, orderCost K f x = f (max x s)) ∧
      (∀ x, orderCost K f x =
        ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x))) ∧
      (∀ x, orderCost K f x ≤ f x) ∧ aux_so_KC K (fun x => orderCost K f x) := by
  have hbot : Tendsto f atBot atTop :=
    hco.mono_left (by rw [cocompact_eq_atBot_atTop]; exact le_sup_left)
  obtain ⟨y₀, hy₀⟩ := hc.exists_forall_le hco
  -- the least minimizer
  set Mset := {y | ∀ x, f y ≤ f x} with hMset
  have hMcl : IsClosed Mset := by
    simp only [hMset, Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le hc continuous_const
  obtain ⟨R, hR⟩ := (tendsto_atBot_atTop.1 hbot) (f y₀ + 1)
  have hMbdd : BddBelow Mset := by
    refine ⟨R, fun y hy => ?_⟩
    by_contra h
    push_neg at h
    have := hR y h.le
    have := hy y₀
    linarith
  have hMne : Mset.Nonempty := ⟨y₀, hy₀⟩
  set S := sInf Mset with hSdef
  have hSM : S ∈ Mset := hMcl.csInf_mem hMne hMbdd
  have hSmin : ∀ x, f S ≤ f x := hSM
  -- the reorder point
  set A := {x | x ≤ S ∧ K + f S ≤ f x} with hAdef
  have hAcl : IsClosed A := (isClosed_le continuous_id continuous_const).inter
    (isClosed_le continuous_const hc)
  obtain ⟨R', hR'⟩ := (tendsto_atBot_atTop.1 hbot) (K + f S)
  have hAne : A.Nonempty := ⟨min R' S, min_le_right _ _, hR' _ (min_le_left _ _)⟩
  have hAbdd : BddAbove A := ⟨S, fun x hx => hx.1⟩
  set s := sSup A with hsdef
  have hsA : s ∈ A := hAcl.csSup_mem hAne hAbdd
  have hsS : s < S := by
    rcases lt_or_eq_of_le hsA.1 with h | h
    · exact h
    · exfalso
      have := hsA.2
      rw [h] at this
      linarith
  have hfs : f s = K + f S := by
    have hmem : K + f S ∈ Set.Icc (f S) (f s) := ⟨by linarith, hsA.2⟩
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hsS.le hc.continuousOn hmem
    have hcA : c ∈ A := ⟨hc1.2, hc2.ge⟩
    have : c ≤ s := le_csSup hAbdd hcA
    have hcs : c = s := le_antisymm this hc1.1
    rw [← hcs, hc2]
  -- key facts
  have F1 : ∀ x, x ≤ s → K + f S ≤ f x := by
    intro x hx
    have h3 := aux_so_KC_three hkc hx hsS.le (lt_of_le_of_lt hx hsS)
    rw [hfs] at h3
    have hpos : 0 < S - s := by linarith
    have : (S - s) * (K + f S) ≤ (S - s) * f x := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  have F2 : ∀ x, s < x → x ≤ S → f x < K + f S := by
    intro x hx hxS
    by_contra h
    push_neg at h
    have : x ≤ s := le_csSup hAbdd ⟨hxS, h⟩
    linarith
  have F3 : ∀ x y, S ≤ x → x ≤ y → f x < K + f y := by
    intro x y hx hxy
    rcases lt_or_eq_of_le hxy with h | h
    · have hSy : S < y := lt_of_le_of_lt hx h
      have h3 := aux_so_KC_three hkc hx hxy hSy
      have h4 : (y - x) * f S < (y - x) * (K + f y) :=
        mul_lt_mul_of_pos_left (by linarith [hSmin y]) (by linarith)
      have hpos : 0 < y - S := by linarith
      have : (y - S) * f x < (y - S) * (K + f y) := by nlinarith
      exact lt_of_mul_lt_mul_left this hpos.le
    · rw [h]; linarith
  have F4 : ∀ x y, s < x → x ≤ y → f x < K + f y := by
    intro x y hx hxy
    rcases le_or_gt x S with h | h
    · linarith [F2 x hx h, hSmin y]
    · exact F3 x y h.le hxy
  have lower : ∀ x y, x ≤ y → f (max x s) ≤ K * setupIndicator (y - x) + f y := by
    intro x y hxy
    rcases le_or_gt x s with hx | hx
    · rw [max_eq_right hx, hfs]
      by_cases hy : 0 < y - x
      · simp only [setupIndicator, hy, if_true, mul_one]
        linarith [hSmin y]
      · have : y = x := by linarith
        subst this
        simp only [setupIndicator, sub_self, lt_irrefl, if_false, mul_zero, zero_add]
        exact F1 y hx
    · rw [max_eq_left hx.le]
      by_cases hy : 0 < y - x
      · simp only [setupIndicator, hy, if_true, mul_one]
        exact (F4 x y hx hxy).le
      · have : y = x := by linarith
        simp [setupIndicator, this]
  have attain : ∀ x, ∃ y, x ≤ y ∧ K * setupIndicator (y - x) + f y = f (max x s) := by
    intro x
    rcases le_or_gt x s with hx | hx
    · refine ⟨S, by linarith, ?_⟩
      have : 0 < S - x := by linarith
      simp only [setupIndicator, this, if_true, mul_one, max_eq_right hx, hfs]
    · refine ⟨x, le_rfl, ?_⟩
      simp [setupIndicator, max_eq_left hx.le]
  have hJ : ∀ x, orderCost K f x = f (max x s) := by
    intro x
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
    unfold orderCost
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} =>
        K * setupIndicator ((y : ℝ) - x) + f y) := by
      refine ⟨f (max x s), ?_⟩
      rintro _ ⟨y, rfl⟩
      exact lower x y y.2
    apply le_antisymm
    · obtain ⟨y, hy, heq⟩ := attain x
      exact (ciInf_le hbdd ⟨y, hy⟩).trans_eq heq
    · exact le_ciInf fun y => lower x y y.2
  have hQ : ∀ x, orderCost K f x =
      ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x)) := by
    intro x
    rw [hJ x]
    symm
    have hbdd : BddBelow (Set.range fun q : ℚ =>
        K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x)) := by
      refine ⟨f (max x s), ?_⟩
      rintro _ ⟨q, rfl⟩
      exact lower x _ (le_max_right _ _)
    apply le_antisymm
    · rcases le_or_gt x s with hx | hx
      · by_contra hlt
        push_neg at hlt
        set c₀ := ⨅ q : ℚ, (K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x))
        rw [max_eq_right hx, hfs] at hlt
        have hε : 0 < c₀ - K - f S := by linarith
        obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hc S (c₀ - K - f S) hε
        have hxS : max x (S - δ) < S := max_lt (by linarith) (by linarith)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hxS
        have hqx : x < q := lt_of_le_of_lt (le_max_left _ _) hq1
        have hqd : S - δ < q := lt_of_le_of_lt (le_max_right _ _) hq1
        have hfq : f q < c₀ - K := by
          have := hδf q (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
          rw [Real.dist_eq, abs_lt] at this
          linarith [this.2]
        have hle : c₀ ≤ K * setupIndicator (max (q : ℝ) x - x) + f (max (q : ℝ) x) :=
          ciInf_le hbdd q
        have hmax : max (q : ℝ) x = q := max_eq_left hqx.le
        have hpos : 0 < (q : ℝ) - x := by linarith
        have hind : setupIndicator ((q : ℝ) - x) = 1 := by simp [setupIndicator, hpos]
        rw [hmax, hind] at hle
        linarith
      · obtain ⟨q, hq⟩ := exists_rat_lt x
        have hle := ciInf_le hbdd q
        have hmax : max (q : ℝ) x = x := max_eq_right hq.le
        simp only [hmax, sub_self, setupIndicator, lt_irrefl, if_false, mul_zero,
          zero_add] at hle
        rw [max_eq_left hx.le]
        exact hle
    · exact le_ciInf fun q => lower x _ (le_max_right _ _)
  refine ⟨S, s, ⟨hSM, fun y hy => csInf_le hMbdd hy⟩, ⟨?_, ?_⟩, hsS, hfs, hJ, hQ, ?_, ?_⟩
  · -- s is in the reorder set
    show reorderGap K f s ≤ 0
    unfold reorderGap
    have : Nonempty {y : ℝ // s ≤ y} := ⟨⟨s, le_rfl⟩⟩
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // s ≤ y} => f y) :=
      ⟨f S, by rintro _ ⟨y, rfl⟩; exact hSmin y⟩
    have : (⨅ y : {y : ℝ // s ≤ y}, f y) = f S :=
      le_antisymm (ciInf_le hbdd ⟨S, hsS.le⟩) (le_ciInf fun y => hSmin y)
    rw [this, hfs]; linarith
  · intro x hx
    change reorderGap K f x ≤ 0 at hx
    by_contra hxs
    push_neg at hxs
    obtain ⟨y, hy, hymin⟩ := aux_so_min_attained hc hco x
    unfold reorderGap at hx
    have : Nonempty {y : ℝ // x ≤ y} := ⟨⟨x, le_rfl⟩⟩
    have hbdd : BddBelow (Set.range fun y : {y : ℝ // x ≤ y} => f y) :=
      ⟨f S, by rintro _ ⟨y, rfl⟩; exact hSmin y⟩
    have : (⨅ y : {y : ℝ // x ≤ y}, f y) = f y :=
      le_antisymm (ciInf_le hbdd ⟨y, hy⟩) (le_ciInf fun z => hymin z z.2)
    rw [this] at hx
    have := F4 x y hxs hy
    linarith
  · intro x
    rw [hJ x]
    rcases le_or_gt x s with hx | hx
    · rw [max_eq_right hx, hfs]; exact F1 x hx
    · rw [max_eq_left hx.le]
  · -- K-convexity of the optimal cost
    have hfun : (fun x => orderCost K f x) = fun x => f (max x s) := funext hJ
    rw [hfun]
    intro x₁ x₂ hx θ h0 h1
    beta_reduce
    set x := θ * x₁ + (1 - θ) * x₂ with hxdef
    have hx1 : x₁ ≤ x := by nlinarith
    have hx2 : x ≤ x₂ := by nlinarith
    rcases lt_or_ge s x₁ with hs1 | hs1
    · rw [max_eq_left (by linarith : s ≤ x), max_eq_left hs1.le,
        max_eq_left (by linarith : s ≤ x₂)]
      exact hkc x₁ x₂ hx θ h0 h1
    · rw [max_eq_right hs1]
      rcases le_or_gt x₂ s with hs2 | hs2
      · rw [max_eq_right (by linarith : x ≤ s), max_eq_right hs2]
        nlinarith
      · rw [max_eq_left hs2.le]
        have hD : f s ≤ K + f x₂ := by rw [hfs]; linarith [hSmin x₂]
        rcases le_or_gt x s with hxs | hxs
        · rw [max_eq_right hxs]
          nlinarith
        · rw [max_eq_left hxs.le]
          have h3 := aux_so_KC_three hkc hxs.le hx2 hs2
          have hprod : 0 ≤ θ * (K + f x₂ - f s) * (s - x₁) :=
            mul_nonneg (mul_nonneg h0 (by linarith)) (by linarith)
          have hpos : 0 < x₂ - s := by linarith
          have : (x₂ - s) * f x ≤ (x₂ - s) * (θ * f s + (1 - θ) * (K + f x₂)) := by
            rw [hxdef] at h3 ⊢
            nlinarith
          exact le_of_mul_le_mul_left this hpos

variable {L M : ℕ}

noncomputable def aux_so_W (P : Model L M) (p : ℕ) (F : ℝ → (Fin M → ℝ) → ℝ) (y : ℝ)
    (o : Fin M → ℝ) : ℝ :=
  P.G p y + P.α (p + 1) * ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p)

def aux_so_Good (F : ℝ → (Fin M → ℝ) → ℝ) (k : ℝ) : Prop :=
  Measurable (fun q : ℝ × (Fin M → ℝ) => F q.1 q.2) ∧
  (∀ o, Continuous fun x => F x o) ∧
  (∀ o, aux_so_KC k (fun x => F x o)) ∧
  (∃ c, ∀ x o, c ≤ F x o) ∧
  (∃ a b, 0 ≤ b ∧ ∀ x o, F x o ≤ a + b * (|x| + ‖o‖))

lemma aux_so_obsComp_cont (j : ℕ) : Continuous (fun o : Fin M → ℝ => obsComp o j) := by
  unfold obsComp
  by_cases h : j < M
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const

lemma aux_so_obsComp_le (o : Fin M → ℝ) (j : ℕ) : |obsComp o j| ≤ ‖o‖ := by
  unfold obsComp
  split_ifs with h
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm o _
  · simp

lemma aux_so_trans_cont : Continuous (fun z : (ℝ × (Fin M → ℝ)) × (Fin (L + M + 2) → ℝ) =>
    ((nextX z.1.1 z.1.2 z.2, nextO z.1.2 z.2) : ℝ × (Fin M → ℝ))) := by
  refine Continuous.prodMk ?_ ?_
  · unfold nextX
    refine ((continuous_fst.comp continuous_fst).sub ?_).sub
      ((aux_so_obsComp_cont 0).comp (continuous_snd.comp continuous_fst))
    exact continuous_finsetSum _ fun k _ => (continuous_apply _).comp continuous_snd
  · unfold nextO
    refine continuous_pi fun j => ?_
    exact ((aux_so_obsComp_cont _).comp (continuous_snd.comp continuous_fst)).add
      ((continuous_apply _).comp continuous_snd)

lemma aux_so_nextX_le (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    |nextX y o D| ≤ |y| + ((L : ℝ) + 2) * ∑ k, |D k| + ‖o‖ := by
  unfold nextX
  have h1 : |∑ k : Fin (L + 2), D (Fin.castLE (by omega) k)| ≤ ((L : ℝ) + 2) * ∑ k, |D k| := by
    calc _ ≤ ∑ k : Fin (L + 2), |D (Fin.castLE (by omega) k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (L + 2), ∑ k', |D k'| := Finset.sum_le_sum fun k _ =>
          Finset.single_le_sum (f := fun k' => |D k'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ _)
      _ = _ := by simp
  have h2 := aux_so_obsComp_le o 0
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [le_abs_self y, neg_abs_le y]

lemma aux_so_nextO_le (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    ‖nextO o D‖ ≤ ‖o‖ + ∑ k, |D k| := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  unfold nextO
  rw [Real.norm_eq_abs]
  have h1 := aux_so_obsComp_le o (j.val + 1)
  have h2 : |D ⟨L + 2 + j.val, by have := j.isLt; omega⟩| ≤ ∑ k, |D k| :=
    Finset.single_le_sum (f := fun k => |D k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma aux_so_pt_bound {F : ℝ → (Fin M → ℝ) → ℝ} {c a b : ℝ} (hb : 0 ≤ b)
    (hc : ∀ x o, c ≤ F x o) (hab : ∀ x o, F x o ≤ a + b * (|x| + ‖o‖))
    (y : ℝ) (o : Fin M → ℝ) (D : Fin (L + M + 2) → ℝ) :
    ‖F (nextX y o D) (nextO o D)‖ ≤
      (|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k| := by
  rw [Real.norm_eq_abs]
  have h1 := aux_so_nextX_le y o D
  have h2 := aux_so_nextO_le o D
  have hs : 0 ≤ |nextX y o D| + ‖nextO o D‖ := by positivity
  have h3 : b * (|nextX y o D| + ‖nextO o D‖) ≤ b * (|y| + 2 * ‖o‖) + b * ((L : ℝ) + 3) * ∑ k, |D k| := by
    have : |nextX y o D| + ‖nextO o D‖ ≤ (|y| + 2 * ‖o‖) + ((L : ℝ) + 3) * ∑ k, |D k| := by
      linarith
    calc b * (|nextX y o D| + ‖nextO o D‖) ≤ b * ((|y| + 2 * ‖o‖) + ((L : ℝ) + 3) * ∑ k, |D k|) :=
          mul_le_mul_of_nonneg_left this hb
      _ = _ := by ring
  have h4 := hc (nextX y o D) (nextO o D)
  have h5 := hab (nextX y o D) (nextO o D)
  have h6 : 0 ≤ b * (|nextX y o D| + ‖nextO o D‖) := mul_nonneg hb hs
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [le_abs_self a, neg_abs_le c, abs_nonneg a, abs_nonneg c]

lemma aux_so_sumD_int (P : Model L M) (p : ℕ) :
    Integrable (fun D : Fin (L + M + 2) → ℝ => ∑ k, |D k|) (P.μ p) :=
  integrable_finsetSum _ fun k _ => (P.μ_integrable p k).abs

lemma aux_so_meas_D {F : ℝ → (Fin M → ℝ) → ℝ}
    (hF : Measurable (fun q : ℝ × (Fin M → ℝ) => F q.1 q.2)) (y : ℝ) (o : Fin M → ℝ) :
    Measurable (fun D : Fin (L + M + 2) → ℝ => F (nextX y o D) (nextO o D)) := by
  have hc : Continuous (fun D : Fin (L + M + 2) → ℝ =>
      ((nextX y o D, nextO o D) : ℝ × (Fin M → ℝ))) :=
    (aux_so_trans_cont (L := L) (M := M)).comp
      (continuous_const.prodMk continuous_id :
        Continuous fun D : Fin (L + M + 2) → ℝ => ((y, o), D))
  exact hF.comp hc.measurable

lemma aux_so_integrable (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (y : ℝ) (o : Fin M → ℝ) :
    Integrable (fun D => F (nextX y o D) (nextO o D)) (P.μ p) := by
  haveI := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  refine Integrable.mono' ((integrable_const (|c| + |a| + b * (|y| + 2 * ‖o‖))).add ((aux_so_sumD_int P p).const_mul
    (b * ((L : ℝ) + 3)))) (aux_so_meas_D hF.1 y o).aestronglyMeasurable ?_
  exact Eventually.of_forall fun D => aux_so_pt_bound hb hc hab y o D

lemma aux_so_G_cont (P : Model L M) (p : ℕ) : Continuous (P.G p) :=
  continuousOn_univ.1 ((P.G_convex p).continuousOn isOpen_univ)

lemma aux_so_W_cont (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (o : Fin M → ℝ) : Continuous (fun y => aux_so_W P p F y o) := by
  haveI := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  unfold aux_so_W
  refine (aux_so_G_cont P p).add (continuous_const.mul ?_)
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  refine continuousAt_of_dominated (bound := fun D =>
      (|c| + |a| + b * ((|y₀| + 1) + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k|)
    (Eventually.of_forall fun y => (aux_so_integrable P p hF y o).aestronglyMeasurable) ?_
    ((integrable_const _).add ((aux_so_sumD_int P p).const_mul _)) ?_
  · filter_upwards [Metric.ball_mem_nhds y₀ one_pos] with y hy
    refine Eventually.of_forall fun D => (aux_so_pt_bound hb hc hab y o D).trans ?_
    have : |y| ≤ |y₀| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub y y₀
      linarith
    have := mul_le_mul_of_nonneg_left this hb
    nlinarith
  · refine Eventually.of_forall fun D => ?_
    have h1 : Continuous (fun y => nextX y o D) := by
      unfold nextX; exact (continuous_id.sub continuous_const).sub continuous_const
    exact ((hF.2.1 (nextO o D)).comp h1).continuousAt

lemma aux_so_int_const (P : Model L M) (p : ℕ) (c : ℝ) :
    ∫ _D, c ∂(P.μ p) = c := by
  haveI := P.μ_prob p
  simp

lemma aux_so_W_KC (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (hk : P.α (p + 1) * k ≤ P.K p) (o : Fin M → ℝ) :
    aux_so_KC (P.K p) (fun y => aux_so_W P p F y o) := by
  intro y₁ y₂ hy θ h0 h1
  haveI := P.μ_prob p
  have hI := fun y => aux_so_integrable P p hF y o
  have hpt : ∀ D : Fin (L + M + 2) → ℝ, F (nextX (θ * y₁ + (1 - θ) * y₂) o D) (nextO o D) ≤
      θ * F (nextX y₁ o D) (nextO o D) + (1 - θ) * (k + F (nextX y₂ o D) (nextO o D)) := by
    intro D
    have e : nextX (θ * y₁ + (1 - θ) * y₂) o D =
        θ * nextX y₁ o D + (1 - θ) * nextX y₂ o D := by unfold nextX; ring
    rw [e]
    exact hF.2.2.1 (nextO o D) _ _ (by unfold nextX; linarith) θ h0 h1
  have hint2 : Integrable (fun D => θ * F (nextX y₁ o D) (nextO o D) +
      (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) (P.μ p) :=
    ((hI y₁).const_mul θ).add (((integrable_const k).add (hI y₂)).const_mul (1 - θ))
  have hint : ∫ D, F (nextX (θ * y₁ + (1 - θ) * y₂) o D) (nextO o D) ∂(P.μ p) ≤
      θ * ∫ D, F (nextX y₁ o D) (nextO o D) ∂(P.μ p) +
        (1 - θ) * (k + ∫ D, F (nextX y₂ o D) (nextO o D) ∂(P.μ p)) := by
    calc _ ≤ ∫ D, (θ * F (nextX y₁ o D) (nextO o D) +
          (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) ∂(P.μ p) :=
          integral_mono (hI _) hint2 hpt
      _ = _ := by
          have hk2 : Integrable (fun D => k + F (nextX y₂ o D) (nextO o D)) (P.μ p) :=
            (integrable_const k).add (hI y₂)
          have e1 : ∫ D, (θ * F (nextX y₁ o D) (nextO o D) +
              (1 - θ) * (k + F (nextX y₂ o D) (nextO o D))) ∂(P.μ p) =
              ∫ D, θ * F (nextX y₁ o D) (nextO o D) ∂(P.μ p) +
              ∫ D, (1 - θ) * (k + F (nextX y₂ o D) (nextO o D)) ∂(P.μ p) :=
            integral_add ((hI y₁).const_mul θ) (hk2.const_mul (1 - θ))
          have e2 : ∫ D, (k + F (nextX y₂ o D) (nextO o D)) ∂(P.μ p) =
              ∫ _D, k ∂(P.μ p) + ∫ D, F (nextX y₂ o D) (nextO o D) ∂(P.μ p) :=
            integral_add (integrable_const k) (hI y₂)
          rw [e1, integral_const_mul, integral_const_mul, e2, aux_so_int_const]
  have hG := (P.G_convex p).2 (Set.mem_univ y₁) (Set.mem_univ y₂) h0 (by linarith : 0 ≤ 1 - θ)
    (by ring : θ + (1 - θ) = 1)
  simp only [smul_eq_mul] at hG
  unfold aux_so_W
  have hα := P.α_pos (p + 1)
  have h3 := mul_le_mul_of_nonneg_left hint hα.le
  have h4 : 0 ≤ (1 - θ) * (P.K p - P.α (p + 1) * k) := mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma aux_so_W_lower (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k c : ℝ}
    (hF : aux_so_Good F k) (hc : ∀ x o, c ≤ F x o) (y : ℝ) (o : Fin M → ℝ) :
    P.G p y + P.α (p + 1) * c ≤ aux_so_W P p F y o := by
  haveI := P.μ_prob p
  unfold aux_so_W
  have : c ≤ ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p) := by
    calc c = ∫ _D, c ∂(P.μ p) := (aux_so_int_const P p c).symm
      _ ≤ _ := integral_mono (integrable_const c) (aux_so_integrable P p hF y o)
          (fun D => hc _ _)
  have := mul_le_mul_of_nonneg_left this (P.α_pos (p + 1)).le
  linarith

lemma aux_so_W_coer (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (o : Fin M → ℝ) :
    Tendsto (fun y => aux_so_W P p F y o) (cocompact ℝ) atTop := by
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  exact tendsto_atTop_mono (fun y => aux_so_W_lower P p hF hc y o)
    (tendsto_atTop_add_const_right _ _ (P.G_coercive p))

lemma aux_so_W_upper (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) :
    ∃ a b, 0 ≤ b ∧ ∀ y o, aux_so_W P p F y o ≤ a + b * (|y| + ‖o‖) := by
  haveI := P.μ_prob p
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  obtain ⟨a, b, hb, hab⟩ := hF.2.2.2.2
  obtain ⟨aG, bG, hG⟩ := P.G_linearGrowth p
  set E := ∫ D, ∑ k, |D k| ∂(P.μ p) with hE
  set α := P.α (p + 1) with hα
  have hαpos : 0 < α := P.α_pos (p + 1)
  refine ⟨aG + α * (|c| + |a| + b * ((L : ℝ) + 3) * E), |bG| + 2 * α * b, by positivity, ?_⟩
  intro y o
  unfold aux_so_W
  have hint : ∫ D, F (nextX y o D) (nextO o D) ∂(P.μ p) ≤
      (|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * E := by
    calc _ ≤ ∫ D, ((|c| + |a| + b * (|y| + 2 * ‖o‖)) + b * ((L : ℝ) + 3) * ∑ k, |D k|)
          ∂(P.μ p) := integral_mono (aux_so_integrable P p hF y o)
            ((integrable_const _).add ((aux_so_sumD_int P p).const_mul _))
            (fun D => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans
              (aux_so_pt_bound hb hc hab y o D)))
      _ = _ := by
          rw [integral_add (integrable_const _) ((aux_so_sumD_int P p).const_mul _),
            integral_const_mul, aux_so_int_const]
  have hGy : P.G p y ≤ aG + |bG| * |y| := by
    have := hG y
    have := le_abs_self (P.G p y)
    have := mul_le_mul_of_nonneg_right (le_abs_self bG) (abs_nonneg y)
    linarith
  have h1 := mul_le_mul_of_nonneg_left hint hαpos.le
  have h2 : 0 ≤ α * b * |y| := by positivity
  have h3 : 0 ≤ ‖o‖ := norm_nonneg _
  have h4 : 0 ≤ |bG| * ‖o‖ := by positivity
  nlinarith

lemma aux_so_W_meas (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) :
    Measurable (fun q : ℝ × (Fin M → ℝ) => aux_so_W P p F q.1 q.2) := by
  haveI := P.μ_prob p
  unfold aux_so_W
  refine ((aux_so_G_cont P p).measurable.comp measurable_fst).add (measurable_const.mul ?_)
  have hsm : StronglyMeasurable (Function.uncurry fun (q : ℝ × (Fin M → ℝ))
      (D : Fin (L + M + 2) → ℝ) => F (nextX q.1 q.2 D) (nextO q.2 D)) :=
    (hF.1.comp (aux_so_trans_cont (L := L) (M := M)).measurable).stronglyMeasurable
  exact (hsm.integral_prod_right (ν := P.μ p)).measurable

lemma aux_so_setupIndicator_meas : Measurable setupIndicator := by
  unfold setupIndicator
  exact Measurable.ite measurableSet_Ioi measurable_const measurable_const

lemma aux_so_step (P : Model L M) (p : ℕ) {F : ℝ → (Fin M → ℝ) → ℝ} {k : ℝ}
    (hF : aux_so_Good F k) (hk : P.α (p + 1) * k ≤ P.K p) :
    aux_so_Good (fun x o => orderCost (P.K p) (fun y => aux_so_W P p F y o) x) (P.K p) := by
  obtain ⟨c, hc⟩ := hF.2.2.2.1
  have hsc := fun o => aux_so_scarf (P.K_pos p) (aux_so_W_cont P p hF o)
    (aux_so_W_KC P p hF hk o) (aux_so_W_coer P p hF o)
  choose S s hS hs hsS hfs hJ hQ hle hKC using hsc
  obtain ⟨y₀, hy₀⟩ := (aux_so_G_cont P p).exists_forall_le (P.G_coercive p)
  obtain ⟨a', b', hb', hab'⟩ := aux_so_W_upper P p hF
  refine ⟨?_, ?_, hKC, ?_, ⟨a', b', hb', fun x o => (hle o x).trans (hab' x o)⟩⟩
  · have hfun : (fun q : ℝ × (Fin M → ℝ) =>
        orderCost (P.K p) (fun y => aux_so_W P p F y q.2) q.1) =
        fun q => ⨅ r : ℚ, (P.K p * setupIndicator (max (r : ℝ) q.1 - q.1) +
          aux_so_W P p F (max (r : ℝ) q.1) q.2) := funext fun q => hQ q.2 q.1
    rw [hfun]
    refine Measurable.iInf fun r => ?_
    refine (measurable_const.mul (aux_so_setupIndicator_meas.comp
      ((measurable_const.max measurable_fst).sub measurable_fst))).add ?_
    exact (aux_so_W_meas P p hF).comp ((measurable_const.max measurable_fst).prodMk measurable_snd)
  · intro o
    have : (fun x => orderCost (P.K p) (fun y => aux_so_W P p F y o) x) =
        fun x => aux_so_W P p F (max x (s o)) o := funext (hJ o)
    rw [this]
    exact (aux_so_W_cont P p hF o).comp (continuous_id.max continuous_const)
  · refine ⟨P.G p y₀ + P.α (p + 1) * c, fun x o => ?_⟩
    show _ ≤ orderCost (P.K p) (fun y => aux_so_W P p F y o) x
    rw [hJ o x]
    have := aux_so_W_lower P p hF hc (max x (s o)) o
    have := hy₀ (max x (s o))
    linarith

noncomputable def aux_so_kk (P : Model L M) : ℕ → ℝ
  | 0 => 0
  | n + 1 => P.K (P.T - n)

lemma aux_so_Jgo_succ (P : Model L M) (n : ℕ) :
    P.Jgo (n + 1) = fun x o =>
      orderCost (P.K (P.T - n)) (fun y => aux_so_W P (P.T - n) (P.Jgo n) y o) x := rfl

lemma aux_so_good_all (P : Model L M) :
    ∀ n, n ≤ P.T → aux_so_Good (P.Jgo n) (aux_so_kk P n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨measurable_const, fun _ => continuous_const, fun _ => ?_, ⟨0, fun _ _ => le_rfl⟩,
      ⟨0, 0, le_rfl, fun _ _ => by simp [Model.Jgo]⟩⟩
    intro x₁ x₂ _ θ _ _
    simp [Model.Jgo, aux_so_kk]
  | succ n ih =>
    intro hn
    have hF := ih (by omega)
    rw [aux_so_Jgo_succ]
    apply aux_so_step P (P.T - n) hF
    cases n with
    | zero => simp only [aux_so_kk, mul_zero]; exact (P.K_pos _).le
    | succ m =>
      simp only [aux_so_kk]
      have := P.discount_setup (P.T - (m + 1))
      rw [show P.T - (m + 1) + 1 = P.T - m by omega] at this
      rw [show P.T - (m + 1) + 1 = P.T - m by omega]
      exact this

end GallegoOzerADI.PositiveSetup

open GallegoOzerADI.PositiveSetup

theorem solution {L M : ℕ} [NeZero M] (P : Model L M) (t : ℕ) (ht₁ : 1 ≤ t)
    (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ∃ S s : ℝ, IsLeast {y | ∀ x, P.V t y o ≤ P.V t x o} S ∧
      IsGreatest {x | P.H t x o ≤ 0} s ∧
      ∀ x, (x ≤ s → x < S ∧ P.J t x o = P.K t + P.V t S o) ∧
        (s < x → P.J t x o = P.V t x o) := by
  have hF := aux_so_good_all P (P.T - t) (by omega)
  have hJt : P.J (t + 1) = P.Jgo (P.T - t) := by
    unfold Model.J
    rw [show P.T + 1 - (t + 1) = P.T - t by omega]
  have hV : ∀ y o, P.V t y o = aux_so_W P t (P.Jgo (P.T - t)) y o := by
    intro y o
    simp only [Model.V, aux_so_W, hJt]
  have hk : P.α (t + 1) * aux_so_kk P (P.T - t) ≤ P.K t := by
    rcases h : P.T - t with _ | m
    · simp only [aux_so_kk, mul_zero]; exact (P.K_pos t).le
    · simp only [aux_so_kk]
      rw [show P.T - m = t + 1 by omega]
      exact P.discount_setup t
  obtain ⟨S, s, hS, hs, hsS, hfs, hJ, -, -, -⟩ := aux_so_scarf (P.K_pos t)
    (aux_so_W_cont P t hF o) (aux_so_W_KC P t hF hk o) (aux_so_W_coer P t hF o)
  have hVf : (fun y => P.V t y o) = fun y => aux_so_W P t (P.Jgo (P.T - t)) y o :=
    funext fun y => hV y o
  have hJeq : ∀ x, P.J t x o = aux_so_W P t (P.Jgo (P.T - t)) (max x s) o := by
    intro x
    rw [P.J_eq t ht₁ htT x o, hVf]
    exact hJ x
  refine ⟨S, s, ?_, ?_, fun x => ⟨fun hx => ⟨lt_of_le_of_lt hx hsS, ?_⟩, fun hx => ?_⟩⟩
  · simp only [hV]; exact hS
  · have : {x | P.H t x o ≤ 0} = {x | reorderGap (P.K t)
        (fun y => aux_so_W P t (P.Jgo (P.T - t)) y o) x ≤ 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Model.H, hVf]
    rw [this]; exact hs
  · rw [hJeq, max_eq_right hx, hV]; exact hfs
  · rw [hJeq, max_eq_left hx.le, hV]
