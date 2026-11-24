-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_cmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:28:00.437336+00:00
-- url     : https://prove2.me/submissions/d1f041aa-4b9a-48de-a45f-71ae79391ae7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_cmb_crd
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_quotLocF_mk__fd1bb1b492f4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩
end Formalism.HermitianLattices.Ext.L3.HU
