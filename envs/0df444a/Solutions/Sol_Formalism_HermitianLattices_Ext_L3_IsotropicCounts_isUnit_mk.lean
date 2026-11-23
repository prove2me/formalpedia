-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isUnit_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:08.812244+00:00
-- url     : https://prove2.me/submissions/33a121fd-8e5e-4f2e-b454-43a00ad57442

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MapMkConjTranspose

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}
namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {δ : 𝓞 K} (hδ : Ideal.span {δ} ⊔ extP K 𝔭 = ⊤) (N : ℕ) :
    IsUnit (Ideal.Quotient.mk (extP K 𝔭 ^ N) δ) := by
  have h2 : Ideal.span {δ} ⊔ extP K 𝔭 ^ N = ⊤ := Ideal.sup_pow_eq_top hδ
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h2
  obtain ⟨y, hy, z, hz, hyz⟩ := h2
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hq : Ideal.Quotient.mk (extP K 𝔭 ^ N) (δ * a) = Ideal.Quotient.mk (extP K 𝔭 ^ N) 1 := by
    rw [Ideal.Quotient.eq]
    have hza : δ * a - 1 = -z := by
      rw [← hyz]
      ring
    rw [hza]
    exact neg_mem hz
  rw [map_mul, map_one] at hq
  exact isUnit_iff_exists_inv.mpr ⟨_, hq⟩
end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
