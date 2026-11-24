-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.InI.divK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:10:30.701193+00:00
-- url     : https://prove2.me/submissions/4f9345b8-5b79-44c8-a9b1-2fc338d49578

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_Cell_inI___dc4ac2cc5e49
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_of_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exists_frac
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InI_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_div
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_ne_zero_of_notMem
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_WCA____ne_zero_cf941fa073ca


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.Cell
namespace InI
theorem _root_.solution (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D)
    {v : ℕ} (hv : ¬ InI 𝔭 (v + 1) D) {k : ℕ} {a : K} (ha : InI 𝔭 (v + k) a) :
    InI 𝔭 k (D⁻¹ * a) := by
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hD h0
  have hδv : δ ∉ 𝔭 ^ (v + 1) := fun h =>
    hv (InI.of_mul h𝔭.isPrime ht (by rw [← e]; exact (inI_ι h𝔭).2 h))
  have hδ0 : δ ≠ 0 := fun h => hδv (h ▸ zero_mem _)
  have h1 := InI.div h𝔭 hδ0 hδv ha
  have h2 := InI.mul h𝔭.isPrime (InI.int h𝔭.isPrime (ι t)) h1
  rw [zero_add] at h2
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have hδ0' := κι_ne_zero (K := K) hδ0
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at e
    exact hδ0' e
  have : D⁻¹ * a = κ (ι t) * ((κ (ι δ))⁻¹ * a) := by
    rw [e]
    field_simp
  rw [this]
  exact h2
end InI
end Formalism.HermitianLattices.Ext.L3.Cell
