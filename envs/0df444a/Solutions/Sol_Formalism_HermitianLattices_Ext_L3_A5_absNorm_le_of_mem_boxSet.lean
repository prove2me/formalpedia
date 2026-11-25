-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.A5.absNorm_le_of_mem_boxSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:00:46.169324+00:00
-- url     : https://prove2.me/submissions/23a86ce7-549d-4f4a-9132-768c8fbca3d9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaNOfVdZeroUnit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_box_inter_eq_empty


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.A5
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  by_contra hlt
  have := box_inter_eq_empty hK hF (b := Ideal.span {n}) (not_le.mp hlt)
  have hmem : n ∈ {n' : 𝓞 F | n' ∈ boxSet K F T ∧ n' ∈ Ideal.span {n}} :=
    ⟨hn, Ideal.mem_span_singleton_self n⟩
  rw [this] at hmem
  exact hmem
end Formalism.HermitianLattices.Ext.L3.A5
