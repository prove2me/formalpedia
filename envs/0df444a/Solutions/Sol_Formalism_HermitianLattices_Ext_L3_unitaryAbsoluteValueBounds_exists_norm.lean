-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:59.21234+00:00
-- url     : https://prove2.me/submissions/96ab9a66-b8f7-425e-b9ca-3b9b262d90d4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_one_lt_q
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_beta_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_unit
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_cnt_eq_normRepCount


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) {u : 𝓞 F} (hu : u ∉ 𝔭) :
    ∃ c : 𝓞 K, conjO K c * c - ι u ∈ extP K 𝔭 ^ k := by
  have hq := one_lt_q h𝔭
  have h1 := cnt_unit hK hF h𝔭 (M := 1) le_rfl hk hu
  have h2 := beta_pos (K := K) h𝔭 (M := 1) le_rfl
  have hpos : (0 : ℝ) < (cnt hF 𝔭 k 1 (ι u) : ℝ) := by
    rw [h1]
    exact mul_pos (pow_pos (by linarith) _) h2
  have hpos' : 0 < normRepCount K (extP K 𝔭 ^ k) 1 (ι u) := by
    rw [← cnt_eq_normRepCount hF]
    exact_mod_cast hpos
  unfold normRepCount at hpos'
  obtain ⟨⟨x, y, hy, hsum⟩⟩ := (Nat.card_pos_iff.mp hpos').1
  refine ⟨y 0, ?_⟩
  rw [Fin.sum_univ_one] at hsum
  exact Ideal.Quotient.eq.mp hsum
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
