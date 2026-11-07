-- Prove2me | solution 1 for DualityStability.WeakDuality.hull_conjugate_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:41:04.723195+00:00
-- url     : https://prove2.me/submissions/fd4ad813-fbee-4fd3-8732-77b4c63a6284

import Definitions.Def_DualityStability_WeakDuality_Problem

open Filter Topology

namespace DualityStability.WeakDuality

lemma ereal_neg_iSup' {ι : Sort*} (u : ι → EReal) : -(⨆ i, u i) = ⨅ i, -u i := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.neg_le_neg_iff.mpr (le_iSup u i)
  · rw [EReal.le_neg]
    exact iSup_le fun i => by rw [EReal.le_neg]; exact iInf_le (fun i => -u i) i

lemma ereal_iInf_add_coe' {ι : Sort*} (u : ι → EReal) (c : ℝ) :
    (⨅ i, u i) + c = ⨅ i, (u i + c) := by
  apply le_antisymm
  · exact le_iInf fun i => by gcongr; exact iInf_le u i
  · calc ⨅ i, (u i + c) = (⨅ i, (u i + c)) - c + c := EReal.sub_add_cancel.symm
      _ ≤ (⨅ i, u i) + c := by
        gcongr
        refine le_iInf fun i => ?_
        calc (⨅ i, (u i + c)) - c ≤ u i + c - c := EReal.sub_le_sub (iInf_le _ i) le_rfl
          _ = u i := EReal.add_sub_cancel_right

lemma ereal_iInf_sub_coe' {ι : Sort*} (u : ι → EReal) (c : ℝ) :
    (⨅ i, u i) - c = ⨅ i, (u i - c) := by
  simp only [sub_eq_add_neg, ← EReal.coe_neg]
  exact ereal_iInf_add_coe' u (-c)

lemma ereal_coe_add_iInf' {ι : Sort*} (u : ι → EReal) (c : ℝ) :
    (c : EReal) + (⨅ i, u i) = ⨅ i, ((c : EReal) + u i) := by
  rw [add_comm, ereal_iInf_add_coe']; simp only [add_comm]

lemma ereal_iInf_iInf_add' {ι κ : Sort*} (a : ι → EReal) (c : κ → EReal)
    (hA : (⨅ i, a i) ≠ ⊤) (k0 : κ) (r : ℝ) (hk0 : c k0 = r) :
    ⨅ k, ⨅ i, (a i + c k) = (⨅ i, a i) + ⨅ k, c k := by
  apply le_antisymm
  · by_cases hb : (⨅ i, a i) = ⊥
    · calc ⨅ k, ⨅ i, (a i + c k) ≤ ⨅ i, (a i + c k0) := iInf_le _ k0
        _ = (⨅ i, a i) + c k0 := by rw [hk0, ereal_iInf_add_coe']
        _ = ⊥ := by rw [hb, EReal.bot_add]
        _ ≤ _ := bot_le
    · set A := ⨅ i, a i with hAdef
      have hAr : A = (A.toReal : EReal) := (EReal.coe_toReal hA hb).symm
      calc ⨅ k, ⨅ i, (a i + c k) ≤ ⨅ k, (A + c k) := by
            refine iInf_mono fun k => ?_
            by_cases hck : c k = ⊤
            · rw [hck, EReal.add_top_of_ne_bot hb]; exact le_top
            · by_cases hcb : c k = ⊥
              · rw [hcb]; simp only [EReal.add_bot]; obtain ⟨i⟩ : Nonempty ι := by
                  by_contra hne; rw [not_nonempty_iff] at hne; exact hA (iInf_of_empty _)
                exact iInf_le_of_le i le_rfl
              · rw [← EReal.coe_toReal hck hcb, ereal_iInf_add_coe']
        _ = A + ⨅ k, c k := by rw [hAr, ereal_coe_add_iInf']
  · exact le_iInf fun k => le_iInf fun i => add_le_add (iInf_le a i) (iInf_le c k)


end DualityStability.WeakDuality

open DualityStability.WeakDuality

variable {E E' F F' : Type*}
variable [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
variable [AddCommGroup E'] [Module ℝ E'] [TopologicalSpace E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
variable [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

theorem solution (P : Problem E E' F F') (y' : F') :
    -(P.hullConjugate y') =
        (⨅ y : F, P.hull y - (P.pairF.pair y y' : EReal)) ∧
    (⨅ y : F, P.hull y - (P.pairF.pair y y' : EReal)) =
        (⨅ z : F, P.perturbation z - (P.pairF.pair z y' : EReal)) ∧
    (⨅ z : F, P.perturbation z - (P.pairF.pair z y' : EReal)) =
        P.dualMaximand y' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Problem.hullConjugate, ereal_neg_iSup']
    congr 1; funext y
    rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      add_comm, sub_eq_add_neg]
  · apply le_antisymm
    · refine le_iInf fun z => iInf_le_of_le z ?_
      apply EReal.sub_le_sub _ le_rfl
      apply Filter.liminf_le_of_frequently_le'
      rw [Filter.frequently_iff]
      intro U hU
      exact ⟨z, mem_of_mem_nhds hU, le_rfl⟩
    · refine le_iInf fun y => ?_
      set m := ⨅ z : F, P.perturbation z - (P.pairF.pair z y' : EReal) with hm
      rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
      have hℓ : Continuous (fun z : F => ((P.pairF.pair z y' : ℝ) : EReal)) :=
        continuous_coe_real_ereal.comp (P.pairF.continuous_left y')
      have htend : Tendsto (fun z : F => m + (P.pairF.pair z y' : EReal)) (𝓝 y)
          (𝓝 (m + (P.pairF.pair y y' : EReal))) := by
        have hc := EReal.continuousAt_add (p := (m, ((P.pairF.pair y y' : ℝ) : EReal)))
          (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
        exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds (hℓ.tendsto y))
      rw [← htend.liminf_eq]
      unfold Problem.hull
      exact Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun z => EReal.add_le_of_le_sub (iInf_le _ z))
        (by isBoundedDefault) (by isBoundedDefault)
  · -- the computation of Theorem 3
    have hpt : ∀ z : F, P.perturbation z - (P.pairF.pair z y' : EReal) =
        ⨅ x : E, (P.f x - P.g (P.A x - z) - (P.pairF.pair z y' : EReal)) := by
      intro z; rw [Problem.perturbation, ereal_iInf_sub_coe']
    simp_rw [hpt]
    rw [iInf_comm]
    have hre : ∀ x : E, (⨅ z : F, (P.f x - P.g (P.A x - z) - (P.pairF.pair z y' : EReal))) =
        ⨅ y : F, ((((P.pairF.pair y y' : ℝ) : EReal) - P.g y) +
          (P.f x - ((P.pairE.pair x (P.Astar y') : ℝ) : EReal))) := by
      intro x
      rw [← (Equiv.subLeft (P.A x)).iInf_comp]
      congr 1; funext y
      simp only [Equiv.subLeft_apply, sub_sub_cancel, map_sub, LinearMap.sub_apply, P.adjoint]
      have hneg : -(((P.pairE.pair x (P.Astar y') - P.pairF.pair y y' : ℝ)) : EReal) =
          ((P.pairF.pair y y' : ℝ) : EReal) + ((-(P.pairE.pair x (P.Astar y')) : ℝ) : EReal) := by
        rw [← EReal.coe_neg, ← EReal.coe_add]; congr 1; ring
      rw [sub_eq_add_neg (P.f x - _), hneg]
      simp only [sub_eq_add_neg, EReal.coe_neg]
      ac_rfl
    simp_rw [hre]
    obtain ⟨y1, hy1⟩ := P.g_proper_concave.2.2
    obtain ⟨x0, hx0⟩ := P.f_proper_convex.2.2
    have hgr : P.g y1 = (P.g y1).toReal := (EReal.coe_toReal (P.g_proper_concave.2.1 y1) hy1).symm
    have hfr : P.f x0 = (P.f x0).toReal := (EReal.coe_toReal hx0 (P.f_proper_convex.2.1 x0)).symm
    rw [ereal_iInf_iInf_add' _ _ ?_ x0
      ((P.f x0).toReal - P.pairE.pair x0 (P.Astar y')) (by rw [hfr]; rfl)]
    · rw [Problem.dualMaximand, Problem.gstar, Problem.fstar, sub_eq_add_neg (⨅ y : F, _),
        ereal_neg_iSup']
      congr 1; congr 1; funext x
      rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
        add_comm, sub_eq_add_neg]
    · refine ne_top_of_le_ne_top ?_ (iInf_le _ y1)
      rw [hgr, ← EReal.coe_sub]; exact EReal.coe_ne_top _

