-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.op_minor_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:09.656276+00:00
-- url     : https://prove2.me/submissions/6fdcd2f8-bce9-4d6d-9cbc-ccbeb37a3bc4

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowOp_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_opA_top
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minor_mem
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_count_le_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_count_total
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mono
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_mono
import Theorems.Thm_Formalism_G_LogCR_Agree_mono
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 p : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (hp : p ≤ N0) (I : Fin p → Fin N1)
    (mono : ZV d N0 N1 →₀ ℕ)
    (hm : mono ∈ (Matrix.of fun (r r' : Fin p) =>
      rowOp (N1 := N1) TT T s ⟨r.val, lt_of_lt_of_le r.isLt hp⟩ (I r')).det.support) :
    (∀ s' k, s' ≠ s → rowDeg s' k mono = 0) ∧ (∑ k, rowDeg s k mono) = p ∧
      (∀ k, rowDeg s k mono ≤ 1) ∧
      (s ∈ TT → 1 ≤ p → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 mono = 1 ∧
        ∀ k : Fin N0, k.val ≠ 0 → rowDeg s k mono ≤ if 2 ≤ p then 1 else 0) := by
  classical
  simp only [rowOp_eq] at hm
  obtain ⟨τ, hτ, ⟨π, hπ⟩, rfl⟩ := op_minor_mem s
    (fun (r : Fin p) j => opA TT T s ⟨r.val, lt_of_lt_of_le r.isLt hp⟩ j) I mono hm
  simp only [rowDeg_shape, if_true]
  refine ⟨fun s' k hs => if_neg hs, shape_count_total τ, fun k => shape_count_le_one τ hτ k, ?_⟩
  intro hs hp1 k0 hk0
  have hiff : ∀ i, (π i).val = 0 ↔ τ i = k0 := by
    intro i
    rw [opA_top TT T s hs _ _ (hπ i)]
    constructor
    · intro h
      exact Fin.ext (h.trans hk0.symm)
    · intro h
      rw [h, hk0]
  set i0 : Fin p := π.symm ⟨0, hp1⟩ with hi0
  have hnone : (Finset.univ.filter (fun i => τ i = k0)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨i0, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ← hiff i, hi0]
    constructor
    · intro h
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h
    · intro h
      rw [h, Equiv.apply_symm_apply]
  refine ⟨hnone, fun k hk => ?_⟩
  split_ifs with h2
  · exact shape_count_le_one τ hτ _
  · have htot := shape_count_total τ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0), hnone] at htot
    have hne : k ≠ k0 := fun h => hk (h ▸ hk0)
    have hle : (Finset.univ.filter (fun i => τ i = k)).card ≤
        ∑ j ∈ Finset.univ.erase k0, (Finset.univ.filter (fun i => τ i = j)).card :=
      Finset.single_le_sum (f := fun j : Fin N0 => (Finset.univ.filter (fun i => τ i = j)).card)
        (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩)
    omega
end Formalism.DworkPowerSeriesWeights
