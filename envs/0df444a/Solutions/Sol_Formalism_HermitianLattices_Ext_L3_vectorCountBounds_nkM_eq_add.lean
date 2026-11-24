-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkM_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:20.998889+00:00
-- url     : https://prove2.me/submissions/e8d4ce94-9219-4c07-b80e-21e430ed57d1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_finite_vec

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.vectorCountBounds
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n + nkB 𝔭 k c H n := by
  classical
  haveI := finite_vec (m := m) (K := K) h𝔭 k
  unfold nkM nkQ nkB
  have e1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  have e2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // ¬ Qc 𝔭 k c H x ∧
      fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {y : {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k //
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} // ¬ Qc 𝔭 k c H y.1} :=
    Nat.card_congr ((Equiv.subtypeEquivRight (fun x => and_comm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  rw [e1, e2, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl _).symm
end Formalism.HermitianLattices.Ext.L3.vectorCountBounds
