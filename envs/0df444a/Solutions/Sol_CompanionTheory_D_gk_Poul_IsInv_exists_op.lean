-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.IsInv.exists_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:06:17.863884+00:00
-- url     : https://prove2.me/submissions/f9141e4f-9545-4f63-a050-b28b0ead2b42

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Garding
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_sub
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsSmForm_continuous
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_swap
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_left
import Theorems.Thm_CompanionTheory_D_gk_Poul_IsInv_exists_rep
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_sub
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_apply_mem_orbSpan
import Theorems.Thm_CompanionTheory_D_Upq_Sm_exists_approx
import Theorems.Thm_CompanionTheory_D_Upq_Sm_isSm_of_mem_orbSpan
import Theorems.Thm_CompanionTheory_D_gk_Poul_exists_op_of_form
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_schur
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
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
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {hG : IsMatGroup G}
variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : Mat n → (H →L[ℂ] H)} {σ' : Mat n → (H' →L[ℂ] H')}
variable {ι ι' : Type} [Fintype ι] [Fintype ι'] {W : ι → List (Mat n)} {W' : ι' → List (Mat n)} {C : ℝ}
  {B : H → H' → ℂ}
namespace CompanionTheory.D.gk.Poul
namespace IsInv
theorem _root_.solution [(haar : Measure (MG G hG)).IsInvInvariant] (θ : Mat n →L[ℝ] Mat n)
    (hθ : ∀ x ∈ G, θ x = x⁻¹) (hB : IsInv G σ σ' W W' C B) (h : RepOn G σ) (h' : RepOn G σ')
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g ∈ G, ∀ v, ‖σ' g v‖ = ‖v‖)
    (hc : ∀ v, ContinuousOn (fun g => σ g v) G) (hc' : ∀ v, ContinuousOn (fun g => σ' g v) G)
    (hirr : PI.UpqRep.IsIrredOn G σ) (hirr' : PI.UpqRep.IsIrredOn G σ')
    (hW : ∀ i, LieW G (W i)) (hW' : ∀ j, LieW G (W' j)) [Nontrivial H] [Nontrivial H'] :
    ∃ T : H' →L[ℂ] H, (∀ g ∈ G, ∀ y, T (σ' g y) = σ g (T y)) ∧
      ∀ x y, IsSm G σ x → IsSm G σ' y → B x y = ⟪T y, x⟫_ℂ := by
  obtain ⟨y₀, z₀, hy₀s, hy₀, hz₀⟩ := hB.exists_rep (hG := hG) θ hθ h h' hiso hc' hW hW'
  obtain ⟨x₀, w₀, hx₀s, hx₀, hw₀⟩ := hB.swap.exists_rep (hG := hG) θ hθ h' h hiso' hc hW' hW
  obtain ⟨T, hT, hTB⟩ := exists_op_of_form (σ := homMG hG h) (σ' := homMG hG h') (fun g => hiso _ g.mem)
    (fun g => hiso' _ g.mem)
    (FinOfPIAux.schur (homMG hG h') (fun g => hiso' _ g.mem) fun S hS hinv =>
      hirr' S hS fun g hg => hinv (MG.mk hG g hg))
    {x | IsSm G σ x} {y | IsSm G σ' y} (fun g x hx => IsSm.apply h hx g.mem) (fun g y hy => IsSm.apply h' hy g.mem) B
    (fun g x hx y hy => hB.inv _ g.mem x y hx hy) hy₀s hy₀ hz₀
  have hT' : ∀ g ∈ G, ∀ y, T (σ' g y) = σ g (T y) := fun g hg y => hT (MG.mk hG g hg) y
  refine ⟨T, hT', fun x y hx hy => ?_⟩
  have h0 : ∀ y, IsSm G σ' y → B x₀ y = ⟪T y, x₀⟫_ℂ := hTB x₀ hx₀s w₀ fun y hy => by
    have := congrArg star (hw₀ y hy)
    rw [star_star] at this
    rw [this, Complex.star_def, inner_conj_symm]
  have horb : ∀ a ∈ orbSpan G σ x₀, B a y = ⟪T y, a⟫_ℂ := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, hg, rfl⟩ := ha
      have hg' := (hG.2.2.2 g hg).1
      have e : σ' g (σ' g⁻¹ y) = y := by
        rw [← h'.apply_mul hg hg', (hG.2.2.2 g hg).2, h'.map_one]; rfl
      have hy' := hy.apply h' hg'
      calc B (σ g x₀) y = B (σ g x₀) (σ' g (σ' g⁻¹ y)) := by rw [e]
        _ = ⟪T (σ' g⁻¹ y), x₀⟫_ℂ := by rw [hB.inv g hg _ _ hx₀s hy', h0 _ hy']
        _ = ⟪σ g (T (σ' g⁻¹ y)), σ g x₀⟫_ℂ :=
          ((⟨(σ g : H →ₗ[ℂ] H), hiso g hg⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).symm
        _ = _ := by rw [← hT' g hg, e]
    | zero => simpa using hB.smul_left 0 0 y IsSm.zero hy
    | add a b ha hb iha ihb =>
      rw [hB.add_left a b y (isSm_of_mem_orbSpan h hx₀s ha) (isSm_of_mem_orbSpan h hx₀s hb) hy, iha, ihb,
        inner_add_right]
    | smul c a ha iha => rw [hB.smul_left c a y (isSm_of_mem_orbSpan h hx₀s ha) hy, iha, inner_smul_right]
  have hd : Dense (orbSpan G σ x₀ : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    refine (hirr _ (Submodule.isClosed_topologicalClosure _) fun g hg v hv => ?_).resolve_left fun h0 => hx₀ ?_
    · exact map_mem_closure (σ g).continuous hv fun y hy => apply_mem_orbSpan h hg hy
    · have hm : x₀ ∈ orbSpan G σ x₀ := Submodule.subset_span ⟨1, h.one_mem, by simp [h.map_one]⟩
      have := Submodule.le_topologicalClosure _ hm
      rwa [h0, Submodule.mem_bot] at this
  set C' := |C * ∑ j, ‖dsW σ' (W' j) y‖| * Fintype.card ι + ‖T y‖ with hC'
  have hC0 : 0 ≤ C' := by positivity
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨a, ha, hxa⟩ := exists_approx hG h hiso hx₀s hd hx (ι := Option ι) (W := fun o => o.elim [] W)
    (fun o => by
      cases o with
      | none => exact fun X hX => absurd hX List.not_mem_nil
      | some i => exact hW i) (δ := δ / (C' + 1)) (by positivity)
  have has := isSm_of_mem_orbSpan h hx₀s ha
  have e : B x y - ⟪T y, x⟫_ℂ = B (x - a) y - ⟪T y, x - a⟫_ℂ := by
    rw [(hB.left hy).sub hx has, inner_sub_right, horb a ha]; ring
  have h1 : ‖B (x - a) y‖ ≤ |C * ∑ j, ‖dsW σ' (W' j) y‖| * (Fintype.card ι * (δ / (C' + 1))) := by
    refine ((hB.left hy).bd _ (hx.sub has)).trans (mul_le_mul (le_abs_self _) ?_
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _))
    refine (Finset.sum_le_sum fun i _ => (hxa (some i)).le).trans (le_of_eq ?_)
    simp
  have h2 : ‖⟪T y, x - a⟫_ℂ‖ ≤ ‖T y‖ * (δ / (C' + 1)) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hxa none).le (norm_nonneg _))
  rw [e, zero_add]
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans ?_)
  rw [← mul_assoc, ← add_mul, ← hC', ← mul_div_assoc, div_le_iff₀ (by positivity)]
  nlinarith
end IsInv
end CompanionTheory.D.gk.Poul
