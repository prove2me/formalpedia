-- Prove2me | solution 1 for CompanionTheory.D.LK.acycAbs_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:03:45.64779+00:00
-- url     : https://prove2.me/submissions/cbf129e8-7ebb-4505-8c0f-cec89cd76d1e

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MemFiltOfWords
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_CreAnnApply
import Theorems.Thm_CompanionTheory_D_LK_ann_mem
import Theorems.Thm_CompanionTheory_D_LK_cre_mem
import Theorems.Thm_CompanionTheory_D_LK_cre_ann_apply
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_ann_cre
import Theorems.Thm_CompanionTheory_D_LK_bd_apply
import Theorems.Thm_CompanionTheory_D_LK_cre_ne
import Theorems.Thm_CompanionTheory_D_LK_filter_erase_of_not
import Theorems.Thm_CompanionTheory_D_LK_lift_ann
import Theorems.Thm_CompanionTheory_D_LK_lift_cre
import Theorems.Thm_CompanionTheory_D_LK_sup_bd
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_cre_ann_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_euler_filt
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_homotopy_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICKoszul_mem_filt_succ
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
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℂ Z]
namespace CompanionTheory.D.LK
theorem _root_.solution (hS : BdSq) : AcycAbs := by
  intro n ε Z _ _ E a d Fil hE hF B j x hx hcyc
  let I := {i : Pos n // cpt ε i}
  let H : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (d i.1) : Module.End ℂ (Cn n Z)) * cre i.1
  let Da : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * ann i.1
  let N : Module.End ℂ Z := ∑ i : I, a i.1 * d i.1
  let G : ℕ → Submodule ℂ Z := fun k => Nat.casesOn k ⊥ Fil
  have hda : ∀ i j : I, d i.1 * a j.1 - a j.1 * d i.1 = if i = j then 1 else 0 := fun i j => by
    rw [hF.da i.1 j.1 i.2]; simp only [Subtype.ext_iff (a1 := i)]
  have hdG : ∀ i k, ∀ z ∈ G (k + 1), d i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => exact hF.d_zero i z hz
    | succ k => exact hF.d_mem i k z hz
  have hNG : ∀ k, ∀ z ∈ G k, N z ∈ G k := fun k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k =>
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      cases k with
      | zero => rw [Module.End.mul_apply, hF.d_zero _ z hz, map_zero]; exact Submodule.zero_mem _
      | succ k => exact hF.a_mem _ k _ (hF.d_mem _ k z hz)
  have hrG : ∀ i k, ∀ z ∈ G k, E i.1.1 i.1.2 z - a i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k => exact hF.r_mem i k z hz
  have hGf : ∀ k, G k ≤ filt (fun i : I => d i.1) k := fun k => by
    induction k with
    | zero => exact bot_le
    | succ k ih => exact fun z hz => (mem_filt_succ _ _ _).2 fun i => ih (hdG _ k z hz)
  have hGm : ∀ k, G k ≤ G (k + 1) := fun k => by
    cases k with
    | zero => exact bot_le
    | succ k => exact hF.mono (Nat.le_succ k)
  have hH : ∀ (y : Cn n Z) A, H y A = ∑ i : I, d i.1 (cre i.1 y A) := fun y A => by
    simp only [H, LinearMap.sum_apply, Finset.sum_apply]; rfl
  have hHG : ∀ k (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) → ∀ A, H y A ∈ G k := fun k y hy A => by
    rw [hH]; exact Submodule.sum_mem _ fun i _ => hdG _ k _ (cre_mem hy _ _)
  have hρ : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → ∀ A, (bd ε E y - Da y) A ∈ G k := fun k y hy A => by
    have e : Da y A = ∑ i : Pos n, if cpt ε i then a i (ann i y A) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_subtype (p := cpt ε) _ (by simp)]
      simp only [Da, LinearMap.sum_apply, Finset.sum_apply]; rfl
    rw [Pi.sub_apply, bd_apply, e, add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ =>
      Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => ?_)
    · split_ifs
      · exact hrG i _ _ (ann_mem hy _ _)
      · simp
    · split_ifs
      · exact cre_mem (ann_mem (ann_mem hy _) _) _ _
      · exact Submodule.zero_mem _
  have hom : Da * H + H * Da =
      ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * lift n (d i.1) + ∑ i : I, cre i.1 * ann i.1 := by
    refine homotopy_ring (fun i : I => (lift n (a i.1) : Module.End ℂ (Cn n Z))) (fun i => lift n (d i.1))
      (fun i => ann i.1) (fun i => cre i.1) (fun i j => LinearMap.ext fun y => (lift_ann _ _ y).symm)
      (fun i j => LinearMap.ext fun y => (lift_cre _ _ y).symm) (fun i j => ?_) (fun i j => ?_)
    · refine LinearMap.ext fun y => funext fun A => ?_
      have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
      by_cases h : i = j
      · simpa [h] using e
      · simpa [h] using e
    · rw [ann_cre]; simp only [Subtype.ext_iff (a1 := i)]
  have hHs : ∀ y : Cn n Z, Sup ε B (j + 1) y → Sup ε B (j + 2) (H y) := fun y hy A hA => by
    rw [hH] at hA
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
    obtain ⟨h1, h2⟩ := cre_ne (fun h => hi (by rw [h, map_zero]) : cre i.1 y A ≠ 0)
    obtain ⟨e1, e2⟩ := hy _ h2
    rw [filter_erase_of_not (not_not.2 i.2)] at e1
    rw [filter_erase] at e2
    have := card_erase_add_one (mem_filter.2 ⟨h1, i.2⟩ : i.1 ∈ A.filter (cpt ε))
    exact ⟨e1, by omega⟩
  have hΔ : ∀ y : Cn n Z, Sup ε B (j + 1) y → bd ε E y = 0 → ∀ A, bd ε E (H y) A =
      N (y A) + ((j + 1 : ℕ) : ℂ) • y A + ((bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A) := by
    intro y hy hc A
    have e := congrArg (fun T : Module.End ℂ (Cn n Z) => T y A) hom
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      cre_ann_apply, lift_apply] at e
    have e2 : (∑ i : I, if i.1 ∈ A then y A else 0) = ((j + 1 : ℕ) : ℂ) • y A := by
      by_cases h : y A = 0
      · simp [h]
      · rw [← (hy A h).2, ← Finset.sum_subtype (univ.filter (cpt ε)) (p := cpt ε) (by simp)
          (fun i => if i ∈ A then y A else 0), ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
        congr 2
        ext i; simp [and_comm]
    have e3 : N (y A) = ∑ i : I, a i.1 (d i.1 (y A)) := by simp only [N, LinearMap.sum_apply]; rfl
    rw [e3, ← e2, ← e, hc, zero_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
    abel
  have main : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → Sup ε B (j + 1) y → bd ε E y = 0 →
      ∃ t : Cn n Z, Sup ε B (j + 2) t ∧ bd ε E t = y := by
    intro k
    induction k with
    | zero => exact fun y hy _ _ => ⟨0, fun _ h => absurd rfl h, by rw [map_zero]; exact (funext hy).symm⟩
    | succ k ihk =>
      have inner : ∀ m (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) → (∀ A, y A ∈ filt (fun i : I => d i.1) m ⊔ G k) →
          Sup ε B (j + 1) y → bd ε E y = 0 → ∃ t : Cn n Z, Sup ε B (j + 2) t ∧ bd ε E t = y := by
        intro m
        induction m with
        | zero => exact fun y _ hy => ihk y fun A => by simpa [filt] using hy A
        | succ m ih =>
          intro y hy1 hy2 hs hc
          have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
          have hL : ∀ A, (bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A ∈ G k := fun A =>
            Submodule.add_mem _ (hρ k _ (hHG k y hy1) A) (hHG k _ (hρ (k + 1) y hy1) A)
          have hw : ∀ A, (bd ε E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
              (N (y A) - (m : ℂ) • y A) + ((bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A) := fun A => by
            rw [Pi.sub_apply, hΔ y hs hc A, Pi.smul_apply, add_smul]
            abel
          obtain ⟨t, ht, hbt⟩ := ih (bd ε E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
            (fun A => by
              rw [hw]
              exact Submodule.add_mem _ (Submodule.sub_mem _ (hNG (k + 1) _ (hy1 A)) (Submodule.smul_mem _ _ (hy1 A)))
                (hGm k (hL A)))
            (fun A => by
              rw [hw]
              obtain ⟨u, hu, g, hg, e⟩ := Submodule.mem_sup.1 (hy2 A)
              refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL A))
              rw [← e, map_add, smul_add, add_sub_add_comm]
              exact Submodule.add_mem_sup (euler_filt (fun i : I => a i.1) _ (fun i j => hF.d_comm _ _) hda m u hu)
                (Submodule.sub_mem _ (hNG _ _ hg) (Submodule.smul_mem _ _ hg)))
            (fun A hA => by
              by_cases h : y A = 0
              · have := sup_bd E (hHs y hs) (A := A) fun h' => hA (by simp [h, h'])
                exact ⟨this.1, by omega⟩
              · exact hs A h)
            (by
              rw [map_sub, map_smul, hc, smul_zero, sub_zero]
              exact LinearMap.congr_fun (hS n ε Z E hE) _)
          refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
          · by_cases h : t A = 0
            · exact hHs y hs A fun h' => hA (by simp [h, h'])
            · exact ht A h
          · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact fun y hy => inner (k + 1) y hy fun A => Submodule.mem_sup_left (hGf _ (hy A))
  choose f hf using hF.exh
  exact main ((univ.sup fun A => f (x A)) + 1) x
    (fun A => hF.mono (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (hf _)) hx hcyc
end CompanionTheory.D.LK
