-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.proj_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:10.210601+00:00
-- url     : https://prove2.me/submissions/606c1189-bb1d-4e77-b18c-a5840c560cfa

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_inner_sum_psi
import Theorems.Thm_Formalism_HN_QuotientRealization_psi_mem
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_realize
import Theorems.Thm_Formalism_HN_PlaceDecomposition_sum_prj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (x : V) :
    ‖(Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) S :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ.starProjection
        (Formalism.HermitianLatticesTheory.realize b X x)‖ ^ 2 =
      ∑ v, ‖(pv b X (Submodule.span K (S : Set V)) v)ᗮ.starProjection
        (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))‖ ^ 2 := by
  set W := Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) S :
    Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) with hW
  set P := fun v => pv b X (Submodule.span K (S : Set V)) v with hP
  let cv : InfinitePlace K → EuclideanSpace ℂ ι := fun v =>
    (P v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))
  let r := ∑ v, PlaceDecomposition.psi v (WithLp.ofLp (cv v))
  have hρ : ∀ y : V, Formalism.HermitianLatticesTheory.realize b X y =
      ∑ v, PlaceDecomposition.psi v (Formalism.HermitianLatticesTheory.fcoord b X v y) := by
    intro y
    rw [← PlaceDecomposition.sum_prj (Formalism.HermitianLatticesTheory.realize b X y)]
    exact Finset.sum_congr rfl fun v _ => PlaceDecomposition.prj_realize b X v y
  have hr_orth : r ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨s, hs, rfl⟩ := hu
      rw [hρ s, inner_sum_psi]
      refine Finset.sum_eq_zero fun v _ => ?_
      have h1 : WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v s) ∈ P v :=
        Submodule.subset_span ⟨s, Submodule.subset_span hs, rfl⟩
      have h2 : cv v ∈ (P v)ᗮ := Submodule.starProjection_apply_mem _ _
      rw [show (WithLp.toLp 2 (WithLp.ofLp (cv v)) : EuclideanSpace ℂ ι) = cv v from rfl,
        Submodule.inner_right_of_mem_orthogonal h1 h2, Complex.zero_re]
    | zero => exact inner_zero_left _
    | add u w _ _ h1 h2 => rw [inner_add_left, h1, h2, add_zero]
    | smul a u _ h => rw [real_inner_smul_left, h, mul_zero]
  have hdiff : Formalism.HermitianLatticesTheory.realize b X x - r ∈ W := by
    rw [hρ x, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ fun v _ => ?_
    rw [← map_sub]
    have hz : Formalism.HermitianLatticesTheory.fcoord b X v x - WithLp.ofLp (cv v) =
        WithLp.ofLp ((P v).starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))) := by
      simp only [cv, Submodule.starProjection_orthogonal_val, WithLp.ofLp_sub, sub_sub_cancel]
    rw [hz]
    exact psi_mem b X S v _ (Submodule.starProjection_apply_mem _ _)
  have hproj : Wᗮ.starProjection (Formalism.HermitianLatticesTheory.realize b X x) = r := by
    apply Submodule.eq_starProjection_of_mem_orthogonal hr_orth
    rw [Submodule.orthogonal_orthogonal]
    exact hdiff
  rw [hproj, ← real_inner_self_eq_norm_sq, inner_sum_psi]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [show (WithLp.toLp 2 (WithLp.ofLp (cv v)) : EuclideanSpace ℂ ι) = cv v from rfl]
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (cv v)
  rw [RCLike.re_to_complex] at h
  exact h
end Formalism.HN.QuotientRealization
