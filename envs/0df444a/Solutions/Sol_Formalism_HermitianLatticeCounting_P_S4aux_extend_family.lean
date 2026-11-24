-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.extend_family
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:33.207945+00:00
-- url     : https://prove2.me/submissions/b4b9c844-8232-44dd-94a4-4c6b0b79d8b4

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_unit_vec
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂] [Module.Free O abelian₂]
  [Module.Finite O abelian₂] (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (hSD : SelfDual h) {κ : Type} [Fintype κ] (u : κ → abelian₂)
    (horth : ∀ i j, i ≠ j → h (u i) (u j) = 0) (hunit : ∀ i, IsUnit (h (u i) (u i))) (r : ℕ)
    (hr : Fintype.card κ + r ≤ Module.finrank O abelian₂) :
    ∃ t : Fin r → abelian₂, (∀ i j, h (t i) (u j) = 0) ∧ (∀ i j, i ≠ j → h (t i) (t j) = 0) ∧
      ∀ i, IsUnit (h (t i) (t i)) := by
  induction r with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨t, htu, hto, htn⟩ := ih (by omega)
    obtain ⟨c, hc, hcu⟩ := exists_unit_vec h hU hSD (Sum.elim u t)
      (by
        rintro (i | i) (j | j) hne
        · exact horth i j (fun e => hne (by rw [e]))
        · simp only [Sum.elim_inl, Sum.elim_inr]; rw [hSD.1 (t j) (u i), htu, star_zero]
        · exact htu i j
        · exact hto i j (fun e => hne (by rw [e])))
      (by rintro (i | i); exacts [hunit i, htn i])
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    refine ⟨Fin.cons c t, fun i j => ?_, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hc (Sum.inl j)
      · simpa using htu i j
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simpa using hc (Sum.inr j)
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hSD.1 c (t i)]
        have := hc (Sum.inr i)
        simp only [Sum.elim_inr] at this
        rw [this, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact hto i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using htn i
end Formalism.HermitianLatticeCounting.P.S4aux
