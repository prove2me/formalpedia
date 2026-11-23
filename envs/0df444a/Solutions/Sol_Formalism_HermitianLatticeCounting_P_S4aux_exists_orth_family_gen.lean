-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.exists_orth_family_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:56.61471+00:00
-- url     : https://prove2.me/submissions/e607a2e4-066c-47f4-84c4-3ebe153f3ad6

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_exists_unit_vec_gen
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
theorem _root_.solution [Nontrivial O] (J : Ideal O) (hJ : ∀ x ∈ J, ¬ IsUnit x)
    (hpol : ∀ C : Submodule O abelian₂, (∀ c ∈ C, ¬ IsUnit (h c c)) → ∀ c ∈ C, ∀ c' ∈ C, h c c' ∈ J)
    (hSD : SelfDual h) (ρ : ℕ) (hρ : ρ ≤ Module.finrank O abelian₂) :
    ∃ v : Fin ρ → abelian₂, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧ ∀ i, IsUnit (h (v i) (v i)) := by
  induction ρ with
  | zero => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, horth, hunit⟩ := ih (by omega)
    obtain ⟨c, hc, hcu⟩ := exists_unit_vec_gen h J hJ hpol hSD v horth hunit (by rw [Fintype.card_fin]; omega)
    refine ⟨Fin.cons c v, fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · intro hne; exact absurd rfl hne
      · intro _; simp only [Fin.cons_zero, Fin.cons_succ]; exact hc j
      · intro _
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hSD.1 c (v i), hc i, star_zero]
      · intro hne
        simp only [Fin.cons_succ]
        exact horth i j (fun e => hne (by rw [e]))
    · refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hcu
      · simpa using hunit i
end Formalism.HermitianLatticeCounting.P.S4aux
