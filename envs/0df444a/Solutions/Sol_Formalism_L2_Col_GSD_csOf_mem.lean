-- Prove2me | solution 1 for Formalism.L2.Col.GSD.csOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:26.247023+00:00
-- url     : https://prove2.me/submissions/f95bad54-5bd9-4354-a9e2-0f9521fcd373

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
open Formalism.L2.Col.GSD
variable (S : GSD K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) {M : Type} [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (N : Submodule (𝓞 K) M) (F : S.D → M) (hF : ∀ d, F d ∈ N) (n : ℕ)
    (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) : (n : 𝓞 K) • S.csOf h s F ∈ N := by
  unfold csOf
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  obtain ⟨m, hm⟩ := hn c
  have hw : (((S.toCSDOf h s).wt c : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by unfold CSD.wt; exact @Fintype.card_ne_zero _ ((S.toCSDOf h s).finGam c) ⟨1⟩)
  have e1 : ((n : 𝓞 K) • ((((S.toCSDOf h s).wt c : ℕ) : K))⁻¹) = ((m : ℕ) : K) := by
    rw [Algebra.smul_def, map_natCast, hm, Nat.cast_mul, mul_comm, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rw [← smul_assoc, e1, Nat.cast_smul_eq_nsmul]
  exact N.nsmul_mem (hF _) m
end Formalism.L2.Col.GSD
