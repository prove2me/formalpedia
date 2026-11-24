-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.exists_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:10.413801+00:00
-- url     : https://prove2.me/submissions/90bfb52e-3f50-47a6-a9e7-322d0fe9fea5

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_congr
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_add
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_zero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_smul
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsInvariant_topologicalClosure
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}
namespace CompanionTheory.D.gk.FinalFormK
theorem _root_.solution [CompleteSpace H] [CompleteSpace H'] {T : H → H'} (hl : Lin G σ T) (hσ : RepOn G σ) {C : ℝ}
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i))
    (hb : ∀ v, IsSm G σ v → ‖T v‖ ≤ C * ∑ i, ‖dsW σ (W i) v‖) :
    ∃ Λ : ι → (H →L[ℂ] H'), ∀ v, IsSm G σ v → T v = ∑ i, Λ i (dsW σ (W i) v) := by
  classical
  let S : Submodule ℂ H :=
    { carrier := {x | IsSm G σ x}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ hx => hx.smul c }
  let J : S →ₗ[ℂ] PiLp 2 fun _ : ι => H :=
    { toFun := fun x => WithLp.toLp 2 fun i => dsW σ (W i) x
      map_add' := fun x y => PiLp.ext fun i => dsW_add hσ x.2 y.2 (hW i)
      map_smul' := fun c x => PiLp.ext fun i => dsW_smul hσ x.2 c (hW i) }
  let Tl : S →ₗ[ℂ] H' :=
    { toFun := fun x => T x
      map_add' := fun x y => hl.1 _ _ x.2 y.2
      map_smul' := fun c x => hl.2 c _ x.2 }
  let K := (LinearMap.range J).topologicalClosure
  have : CompleteSpace K := (LinearMap.range J).isClosed_topologicalClosure.completeSpace_coe
  let e : S →ₗ[ℂ] K := J.codRestrict K fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  have hd : DenseRange e := by
    refine Subtype.dense_iff.2 fun y hy => closure_mono ?_ hy
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, ⟨x, rfl⟩, rfl⟩
  have hn : ∃ D, ∀ x, ‖Tl x‖ ≤ D * ‖e x‖ := by
    refine ⟨|C| * Fintype.card ι, fun x => (hb _ x.2).trans ?_⟩
    rw [mul_assoc]
    refine mul_le_mul (le_abs_self C) ?_ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
    refine (Finset.sum_le_sum fun i _ => PiLp.norm_apply_le (J x) i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  let Λ : PiLp 2 (fun _ : ι => H) →L[ℂ] H' := Tl.extendOfNorm e ∘L K.orthogonalProjectionOnto
  let s : ι → (H →L[ℂ] PiLp 2 fun _ : ι => H) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => H).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single ℂ (fun _ : ι => H) i
  refine ⟨fun i => Λ ∘L s i, fun v hv => ?_⟩
  have h1 : Λ (J ⟨v, hv⟩) = T v := by
    show Tl.extendOfNorm e (K.orthogonalProjectionOnto (e ⟨v, hv⟩ : PiLp 2 fun _ : ι => H)) = Tl ⟨v, hv⟩
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearMap.extendOfNorm_eq hd hn]
  rw [← h1]
  simp only [ContinuousLinearMap.comp_apply, ← map_sum]
  congr 1
  refine PiLp.ext fun j => ?_
  show dsW σ (W j) v = (∑ i, s i (dsW σ (W i) v)).ofLp j
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne' hij _) (by simp)]
  exact (Pi.single_eq_same (M := fun _ : ι => H) j _).symm
end CompanionTheory.D.gk.FinalFormK
