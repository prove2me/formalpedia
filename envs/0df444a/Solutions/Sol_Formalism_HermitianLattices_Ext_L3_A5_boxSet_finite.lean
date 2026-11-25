-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.boxSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:43.320989+00:00
-- url     : https://prove2.me/submissions/ff4ba402-03af-410b-813e-eaee8085fe2e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => algebraMap F K (n : F)) ?_
    (fun a _ b _ hab => RingOfIntegers.ext ((algebraMap F K).injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ T).subset ?_
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨map_isIntegral_int (algebraMap F K) (RingOfIntegers.isIntegral_coe n), fun φ => ?_⟩
  have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).mpr ⟨_, rfl⟩
  have hc := hK.2.1 φ (algebraMap F K (n : F))
  rw [hst] at hc
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc.symm
  have h1 := hn φ
  simp only at h1 ⊢
  rw [hr] at h1 ⊢
  rw [Complex.ofReal_re] at h1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1.1]
  exact h1.2
end Formalism.HermitianLattices.Ext.L3.A5
