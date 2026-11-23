-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.mem_hcompl_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:49.742095+00:00
-- url     : https://prove2.me/submissions/0a71a877-315f-4fac-9f32-e5693be1b823

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
private theorem algebraMap_int_F_to_K_eq_algebraMap_coe (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
end Formalism.HermitianLattices.Ext.L3.U0
end
end

set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hF : IsFixF K F) {P : Ideal (𝓞 K)} (hP : P.IsPrime) {t : 𝓞 F}
    (ht : t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K))) :
    algebraMap (𝓞 F) (𝓞 K) t ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
  apply Submonoid.subset_closure
  refine ⟨ht, fun u hu => ?_⟩
  have hfix : star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
    rw [algebraMap_int_F_to_K_eq_algebraMap_coe]
    exact (hF _).2 ⟨(t : F), rfl⟩
  rw [hfix] at hu
  have hu' : u = algebraMap (𝓞 F) (𝓞 K) t := IsFractionRing.injective (𝓞 K) K hu
  rw [hu']
  exact ht
end Formalism.HermitianLattices.Ext.L3.U0
