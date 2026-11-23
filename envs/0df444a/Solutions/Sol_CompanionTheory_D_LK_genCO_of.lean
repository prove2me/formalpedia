-- Prove2me | solution 1 for CompanionTheory.D.LK.genCO_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:23.967196+00:00
-- url     : https://prove2.me/submissions/1262c2a1-3f78-47c4-b5e4-841b9305183b

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Theorems.Thm_CompanionTheory_D_LK_differential_commutes_weight_operator
import Theorems.Thm_CompanionTheory_D_LK_free_inter
import Theorems.Thm_CompanionTheory_D_LK_evK_inter
import Theorems.Thm_CompanionTheory_D_LK_evd_Ft_apply
import Theorems.Thm_CompanionTheory_D_LK_lift_evd
import Theorems.Thm_CompanionTheory_D_LK_sup_of_supp
import Theorems.Thm_CompanionTheory_D_LK_Sup_sub
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_sg_mul_self
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
import Theorems.Thm_CompanionTheory_D_LK_bd_apply
import Theorems.Thm_CompanionTheory_D_LK_differential_bounded_support
import Theorems.Thm_CompanionTheory_D_LK_lift_bd
import Theorems.Thm_CompanionTheory_D_LK_sup_bd
import Theorems.Thm_CompanionTheory_D_LK_tri_ne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution (hS : BdSq) (hC : Cover2) : GenCO := by
  intro n ε₀ ε a b h0 hab V _ _ E hE B j
  induction j generalizing V with
  | zero =>
    intro x hx _ _
    obtain ⟨w, hw⟩ := (hab V E hE).2 (x B)
    have hxB : ∀ A, A ≠ B → x A = 0 := fun A hA => by
      by_contra h
      obtain ⟨e1, e2⟩ := hx A h
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 e2 ▸ mem_filter.2 ⟨hi, hc⟩)
    by_cases hB : x B = 0
    · have : x = 0 := funext fun A => by
        by_cases h : A = B
        · rw [h, hB]; rfl
        · exact hxB A h
      subst this
      exact ⟨0, fun A hA => absurd rfl hA, by simp⟩
    have hBn : ∀ i ∈ B, ¬cpt ε₀ i := fun i hi => (mem_filter.1 ((hx B hB).1.symm ▸ hi :)).2
    have hBc : B.filter (cpt ε₀) = ∅ := filter_false_of_mem hBn
    let w' : Cn n V := fun A => ∑ i : Pos n, if cpt ε₀ i ∧ A = insert i B then sg i B • w i else 0
    have hw' : Sup ε₀ B (0 + 1) w' := by
      intro A hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      obtain ⟨h1, rfl⟩ : cpt ε₀ i ∧ A = insert i B := by by_contra h; exact hi (if_neg h)
      rw [filter_insert, if_neg (not_not.2 h1), filter_true_of_mem hBn, filter_insert, if_pos h1, hBc]
      simp
    refine ⟨w', hw', funext fun A => ?_⟩
    by_cases hA : A = B
    · subst hA
      rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hBc]
      have e : (fun c => E c c + (wt (∅ : Finset (Pos n)) c : ℂ) • (1 : Module.End ℂ V)) = fun c => E c c := by
        funext c; simp [wt]
      rw [e, hw, bd_apply, Finset.sum_eq_zero (s := univ) (f := fun i => ∑ j : Pos n, ∑ k : Pos n,
        if Tri ε₀ i j k then cre k (ann j (ann i w')) A else 0), add_zero]
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · have hiA : i ∉ A := fun h => hBn i h hi
          rw [ann_apply, if_neg hiA]
          congr 1
          simp only [w']
          rw [Finset.sum_eq_single i, if_pos ⟨hi, rfl⟩, smul_smul, sg_mul_self, one_smul]
          · intro k _ hk
            refine if_neg fun h => ?_
            rcases mem_insert.1 (h.2 ▸ mem_insert_self i A) with h' | h'
            · exact hk h'.symm
            · exact hiA h'
          · simp
        · rfl
      · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
        split_ifs with ht
        · by_contra h
          exact hBn k (tri_ne h).1 ht.cptk
        · rfl
    · rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hxB A hA, map_zero, map_zero, sub_zero]
      by_contra h
      obtain ⟨e1, e2⟩ := sup_bd E hw' (Ne.symm h)
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 (by omega : (A.filter (cpt ε₀)).card = 0) ▸ mem_filter.2 ⟨hi, hc⟩)
  | succ j ih =>
    intro x hx hr hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε₀ V E hE
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : KRel ε₀ EK := by
      intro a b c d h1 h2
      ext y
      have := LinearMap.congr_fun (hY a b c d h1 h2) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    classical
    let x' : Cn n Y := fun A => if x A = 0 then 0 else (hs (x A)).choose
    have hz : ∀ A, x A = 0 → x' A = 0 := fun A h => if_pos h
    have hx' : Sup ε₀ B (j + 1) x' := sup_of_supp hx hz
    have hr' : Ref ε₀ ε x' := fun A hA => hr A fun h => hA (hz A h)
    have hπx : lift n π x' = x := by
      funext A
      by_cases hA : x A = 0
      · simp [x', hA]
      · simp only [lift_apply, x', if_neg hA]
        exact (hs (x A)).choose_spec
    have hy : ∀ A, bd ε₀ EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd (ε := ε₀) π EY E (fun i _ => hπ _ _) x') A
      rw [hπx, hbx] at this
      exact this
    obtain ⟨s1, -, s3, -⟩ := differential_bounded_support n ε₀ Y EY
    obtain ⟨-, -, s3', -⟩ := differential_bounded_support n ε Y EY
    let y : Cn n (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift n (LinearMap.ker π).subtype y = bd ε₀ EY x' := rfl
    have hyd : Sup ε₀ B j y := sup_of_supp (s1 B j x' hx') fun A hA => Subtype.ext hA
    have hyr : Ref ε₀ ε y := fun A hA =>
      (s3' ε₀ x' h0 hr').2 A fun h => hA (Subtype.ext (by rw [← (s3' ε₀ x' h0 hr').1] at h; exact h))
    have hyb : bd ε₀ EK y = 0 := by
      have := lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _) y
      rw [hιy, show bd ε₀ EY (bd ε₀ EY x') = 0 from LinearMap.congr_fun (hS n ε₀ Y EY hY) x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyr hyb
    have hpush := congrArg (lift n (LinearMap.ker π).subtype) hDw
    have hl : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (φ : V →ₗ[ℂ] W)
        (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W),
        (∀ a b x, φ (E a b x) = F a b (φ x)) → ∀ z : Cn n V,
        lift n φ (lift n (evK ε₀ E a) z) = lift n (evK ε₀ F a) (lift n φ z) :=
      fun φ E F h z => funext fun A => evK_inter φ E F h a _
    rw [map_sub, hl _ EK EY hι, lift_evd _ EK EY hι, lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _), hιy] at hpush
    have c1 : bd ε₀ EY (lift n (evK ε₀ EY a) x') = lift n (evK ε₀ EY a) (bd ε₀ EY x') := by
      rw [(s3' ε₀ x' h0 hr').1, (s3' ε₀ _ h0 fun A hA => hr' A fun h => hA (by simp [h])).1]
      exact (lift_bd _ EY EY (fun i hi z => (LinearMap.congr_fun ((hab Y EY hY).1 i hi).eq z).symm) x').symm
    have c2 : bd ε₀ EY (evd (Ft ε₀ EY) b x') = evd (Ft ε₀ EY) b (bd ε₀ EY x') :=
      free_inter (bd ε₀ EY) _ _
        (fun c z => (LinearMap.congr_fun (differential_commutes_weight_operator n ε₀ ε₀ Y EY (fun _ _ h => h) hY c).eq z).symm) b x'
    obtain ⟨t, ht, hbt⟩ := hac B j
      (lift n (evK ε₀ EY a) x' - evd (Ft ε₀ EY) b x' - lift n (LinearMap.ker π).subtype w)
      (((sup_of_supp hx' fun A h => by simp [h]).sub
        (sup_of_supp hx' fun A h => by rw [evd_Ft_apply, h, map_zero])).sub (sup_of_supp hw fun A h => by simp [h]))
      (by rw [map_sub, map_sub, c1, c2, hpush, sub_self])
    refine ⟨lift n π t, sup_of_supp ht fun A h => by simp [h], ?_⟩
    have h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, hl π EY E hπ, lift_evd π EY E hπ, hπx,
      sub_zero]
end CompanionTheory.D.LK
