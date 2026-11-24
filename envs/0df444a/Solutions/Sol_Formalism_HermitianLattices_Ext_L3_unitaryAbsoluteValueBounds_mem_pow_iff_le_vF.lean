-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.mem_pow_iff_le_vF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.264802+00:00
-- url     : https://prove2.me/submissions/aa7de661-e284-4dc3-bf94-927138e6c097

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldMore
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
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hbdd : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hn
    have hI := Ideal.iInf_pow_eq_bot_of_isDomain (I := 𝔭) h𝔭.ne_top
    rw [← Ideal.mem_bot, ← hI, Ideal.mem_iInf]
    intro i
    obtain ⟨e', he', hie'⟩ := hnb i
    exact Ideal.pow_le_pow_right hie'.le he'
  have hne : {e : ℕ | n ∈ 𝔭 ^ e}.Nonempty := ⟨0, by simp⟩
  unfold vF
  constructor
  · intro he
    exact le_csSup hbdd he
  · intro he
    have hmem : sSup {e : ℕ | n ∈ 𝔭 ^ e} ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem hne hbdd
    exact Ideal.pow_le_pow_right he hmem
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
