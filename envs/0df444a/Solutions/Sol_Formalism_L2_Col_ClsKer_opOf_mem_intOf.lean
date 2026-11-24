-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.opOf_mem_intOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.061804+00:00
-- url     : https://prove2.me/submissions/0e3a6acb-d262-4293-8b37-f849b8cc2d95

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Col
namespace ClsKer
theorem _root_.solution {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (n : ℕ) (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : (n : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by
  intro d'
  show (n : 𝓞 K) • A.appOf h s φ d' ∈ N' d'
  unfold ClsKer.appOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨m, hm⟩ := hn c
  have hw : (((S.toCSDOf h s).wt c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by unfold CSD.wt; exact @Fintype.card_ne_zero _ ((S.toCSDOf h s).finGam c) ⟨1⟩)
  have e1 : ((n : 𝓞 K) • ((((S.toCSDOf h s).wt c : ℕ) : K))⁻¹) = ((m : ℕ) : K) := by
    rw [Algebra.smul_def, map_natCast, hm, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rw [← smul_assoc, e1, Nat.cast_smul_eq_nsmul]
  exact (N' d').nsmul_mem (hk _ d' _ (hφ _)) m
end ClsKer
end Formalism.L2.Col
