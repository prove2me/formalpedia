-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.index_piO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:35.726312+00:00
-- url     : https://prove2.me/submissions/bd9f7a5a-adcc-446e-a5e6-3a827798800f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_span_pow
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (M : ℕ) : (piO O ϖ M).index = q ^ (2 * M) := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex o O) = 2 := by
    rw [← hU.rank2, Module.finrank_eq_card_chooseBasisIndex]
  let NM : AddSubgroup o := (Ideal.span {ϖ ^ M}).toAddSubgroup
  let f : O →+ (Module.Free.ChooseBasisIndex o O → o ⧸ NM) :=
    { toFun := fun y i => QuotientAddGroup.mk (b.repr y i)
      map_zero' := by funext i; simp
      map_add' := fun x y => by funext i; simp }
  have hf : Function.Surjective f := by
    intro g
    choose r hr using fun i => QuotientAddGroup.mk_surjective (g i)
    refine ⟨∑ i, r i • b i, ?_⟩
    funext i
    change QuotientAddGroup.mk (b.repr (∑ i, r i • b i) i) = g i
    rw [← hr i]
    congr 1
    simp [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hker : f.ker = piO O ϖ M := by
    ext y
    rw [AddMonoidHom.mem_ker]
    constructor
    · intro hy
      have h1 : ∀ i, ∃ c, b.repr y i = ϖ ^ M * c := by
        intro i
        have := congrFun hy i
        change QuotientAddGroup.mk (b.repr y i) = (0 : o ⧸ NM) at this
        rw [QuotientAddGroup.eq_zero_iff] at this
        exact Ideal.mem_span_singleton.1 this
      choose c hc using h1
      refine ⟨∑ i, c i • b i, ?_⟩
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, mul_smul, Algebra.smul_def]
    · rintro ⟨z, rfl⟩
      funext i
      change QuotientAddGroup.mk (b.repr (algebraMap o O (ϖ ^ M) * z) i) = (0 : o ⧸ NM)
      rw [QuotientAddGroup.eq_zero_iff, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Ideal.mem_span_singleton.2 (dvd_mul_right _ _)
  have hN : Nat.card (o ⧸ NM) = q ^ M := index_span_pow ϖ hϖ q hq M
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
    AddSubgroup.card_top, Nat.card_fun, hN, Nat.card_eq_fintype_card, hcard, ← pow_mul,
    mul_comm]
end Formalism.HermitianLatticeCounting.P.S4aux
