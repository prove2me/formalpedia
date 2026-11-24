-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.differentIdeal_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:41.162268+00:00
-- url     : https://prove2.me/submissions/c2d2a161-5d0e-47b7-87db-c571059dc3ca

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_adjoin_eq_top
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_minpoly_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  obtain ⟨-, -, hmax⟩ := hK
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hmax P hP
  have hne' : θ ≠ t := fun h => hθt (by rw [h, sub_self]; exact P.zero_mem)
  have hstar : star (algebraMap (𝓞 K) K θ) ≠ algebraMap (𝓞 K) K θ := by
    rw [← ht]; exact fun h => hne' (RingOfIntegers.ext h.symm)
  apply hθt
  apply hle
  rw [← minpoly_eq hF θ t ht hne']
  exact aeval_derivative_mem_differentIdeal (A := 𝓞 F) (K := F) (L := K) θ (adjoin_eq_top hF hstar)
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
