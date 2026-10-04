-- Prove2me | solution 1 for CannonFloydParry.mem_closure_commutator_supp_Icc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T22:49:20.660316+00:00
-- url     : https://prove2.me/submissions/ac152b36-ff3c-4cc6-98f4-fad46e445762

import Definitions.Def_CannonFloydParry
import Mathlib
import Theorems.Thm_CannonFloydParry_mem_F_iff_isThompson
import Theorems.Thm_CannonFloydParry_exists_mem_F_map_partition
import Theorems.Thm_CannonFloydParry_mem_commutator_iff

open CannonFloydParry

namespace CFPSuppIcc

/-- The affine squeeze `t ↦ t/2 + 1/4`, carrying `[0,1]` onto `[1/4, 3/4]`. -/
noncomputable def sig : ℝ ≃o ℝ where
  toFun t := t / 2 + 1 / 4
  invFun t := 2 * t - 1 / 2
  left_inv t := by simp only; ring
  right_inv t := by simp only; ring
  map_rel_iff' := by
    intro s t
    simp only [Equiv.coe_fn_mk]
    constructor <;> intro h <;> linarith

lemma apply_zero (p : UI ≃o UI) : (p ⟨0, zero_mem_UI⟩ : ℝ) = 0 := by
  apply le_antisymm _ (p _).2.1
  have h1 : (⟨0, zero_mem_UI⟩ : UI) ≤ p.symm ⟨0, zero_mem_UI⟩ := (p.symm ⟨0, zero_mem_UI⟩).2.1
  have h2 := p.monotone h1
  rw [p.apply_symm_apply] at h2
  exact h2

lemma apply_one (p : UI ≃o UI) : (p ⟨1, one_mem_UI⟩ : ℝ) = 1 := by
  apply le_antisymm (p _).2.2
  have h1 : p.symm ⟨1, one_mem_UI⟩ ≤ (⟨1, one_mem_UI⟩ : UI) := (p.symm ⟨1, one_mem_UI⟩).2.2
  have h2 := p.monotone h1
  rw [p.apply_symm_apply] at h2
  exact h2

lemma extend_fix_of (p : UI ≃o UI) (s : ℝ)
    (h : ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, (p ⟨s, hs⟩ : ℝ) = s) : extend p s = s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ hs, h hs]
  · rw [extend_apply, extendFun_of_notMem _ hs]

lemma extend_fix_lo (p : UI ≃o UI) {s : ℝ} (hs : s ≤ 0) : extend p s = s := by
  apply extend_fix_of
  intro hm
  have : s = 0 := le_antisymm hs hm.1
  subst this
  exact apply_zero p

lemma extend_fix_hi (p : UI ≃o UI) {s : ℝ} (hs : 1 ≤ s) : extend p s = s := by
  apply extend_fix_of
  intro hm
  have : s = 1 := le_antisymm hm.2 hs
  subst this
  exact apply_one p

lemma extend_mul (p q : UI ≃o UI) (s : ℝ) : extend (p * q) s = extend p (extend q s) := by
  by_cases h : s ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_mem _ h, extendFun_of_mem _ h,
      extendFun_of_mem _ (q ⟨s, h⟩).2]
    rfl
  · rw [extend_apply, extend_apply, extend_apply, extendFun_of_notMem _ h,
      extendFun_of_notMem _ h, extendFun_of_notMem _ h]

lemma extend_one (s : ℝ) : extend (1 : UI ≃o UI) s = s :=
  extend_fix_of _ s (fun _ => rfl)

lemma extend_restrict (L : ℝ ≃o ℝ) (hlo : ∀ x ≤ (0:ℝ), L x = x)
    (hhi : ∀ x, (1:ℝ) ≤ x → L x = x) (s : ℝ) : extend (restrict L hlo hhi) s = L s := by
  by_cases h : s ∈ Set.Icc (0 : ℝ) 1
  · rw [extend_apply, extendFun_of_mem _ h, restrict_coe]
  · rw [extend_apply, extendFun_of_notMem _ h]
    rcases not_and_or.mp h with h' | h'
    · exact (hlo s (le_of_lt (lt_of_not_ge h'))).symm
    · exact (hhi s (le_of_lt (lt_of_not_ge h'))).symm

/-! ### Squeezing a map of `[0,1]` into `[1/4, 3/4]` -/

noncomputable def sqzL (p : UI ≃o UI) : ℝ ≃o ℝ := sig * extend p * sig⁻¹

lemma sqzL_apply (p : UI ≃o UI) (t : ℝ) : sqzL p t = extend p (2 * t - 1 / 2) / 2 + 1 / 4 :=
  rfl

lemma sqzL_lo (p : UI ≃o UI) : ∀ t ≤ (0:ℝ), sqzL p t = t := by
  intro t ht
  rw [sqzL_apply, extend_fix_lo p (by linarith)]
  ring

lemma sqzL_hi (p : UI ≃o UI) : ∀ t, (1:ℝ) ≤ t → sqzL p t = t := by
  intro t ht
  rw [sqzL_apply, extend_fix_hi p (by linarith)]
  ring

noncomputable def sqz (p : UI ≃o UI) : UI ≃o UI := restrict (sqzL p) (sqzL_lo p) (sqzL_hi p)

lemma sqz_coe (p : UI ≃o UI) (z : UI) :
    (sqz p z : ℝ) = extend p (2 * (z : ℝ) - 1 / 2) / 2 + 1 / 4 := rfl

lemma sqz_fix_lo (p : UI ≃o UI) (z : UI) (hz : (z : ℝ) ≤ 1 / 4) : (sqz p z : ℝ) = z := by
  rw [sqz_coe, extend_fix_lo p (by linarith)]
  ring

lemma sqz_fix_hi (p : UI ≃o UI) (z : UI) (hz : 3 / 4 ≤ (z : ℝ)) : (sqz p z : ℝ) = z := by
  rw [sqz_coe, extend_fix_hi p (by linarith)]
  ring

noncomputable def sqzHom : (UI ≃o UI) →* (UI ≃o UI) where
  toFun := sqz
  map_one' := by
    refine DFunLike.ext _ _ (fun z => Subtype.ext ?_)
    show (sqz 1 z : ℝ) = z
    rw [sqz_coe, extend_one]
    ring
  map_mul' p q := by
    refine DFunLike.ext _ _ (fun z => Subtype.ext ?_)
    show (sqz (p * q) z : ℝ) = (sqz p (sqz q z) : ℝ)
    rw [sqz_coe, sqz_coe, sqz_coe, extend_mul]
    have : 2 * (extend q (2 * (z : ℝ) - 1 / 2) / 2 + 1 / 4) - 1 / 2
        = extend q (2 * (z : ℝ) - 1 / 2) := by ring
    rw [this]

/-! ### Dyadic bookkeeping -/

lemma dyadic_sig {t : ℝ} (h : IsDyadic t) : IsDyadic (t / 2 + 1 / 4) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨2 * m + 2 ^ k, k + 2, ?_⟩
  push_cast
  field_simp
  ring

lemma dyadic_sigInv {t : ℝ} (h : IsDyadic t) : IsDyadic (2 * t - 1 / 2) := by
  obtain ⟨m, k, rfl⟩ := h
  refine ⟨4 * m - 2 ^ k, k + 1, ?_⟩
  push_cast
  field_simp
  ring

lemma isThompson_sqz {p : UI ≃o UI} (hp : IsThompson p) : IsThompson (sqz p) := by
  classical
  obtain ⟨B, hBd, hB⟩ := hp
  refine ⟨insert (1 / 4) (insert (3 / 4) (B.image (fun t => t / 2 + 1 / 4))), ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_image] at ht
    rcases ht with rfl | rfl | ⟨s, hs, rfl⟩
    · exact ⟨1, 2, by norm_num⟩
    · exact ⟨3, 2, by norm_num⟩
    · exact dyadic_sig (hBd s hs)
  · intro x y hxy hdis
    have h14 : ¬ ((x : ℝ) < 1 / 4 ∧ 1 / 4 < (y : ℝ)) := by
      rintro ⟨h1, h2⟩
      have hm : (1 / 4 : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((insert (1 / 4) (insert (3 / 4) (B.image (fun t => t / 2 + 1 / 4))) : Finset ℝ) :
            Set ℝ) :=
        ⟨⟨h1, h2⟩, Finset.mem_coe.mpr (Finset.mem_insert_self _ _)⟩
      rw [hdis] at hm
      exact hm
    have h34 : ¬ ((x : ℝ) < 3 / 4 ∧ 3 / 4 < (y : ℝ)) := by
      rintro ⟨h1, h2⟩
      have hm : (3 / 4 : ℝ) ∈ Set.Ioo (x : ℝ) y ∩
          ((insert (1 / 4) (insert (3 / 4) (B.image (fun t => t / 2 + 1 / 4))) : Finset ℝ) :
            Set ℝ) :=
        ⟨⟨h1, h2⟩, Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
      rw [hdis] at hm
      exact hm
    by_cases hy : (y : ℝ) ≤ 1 / 4
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [sqz_fix_lo p z (hz.2.trans hy)]
      simp
    by_cases hx : 3 / 4 ≤ (x : ℝ)
    · refine ⟨0, 0, fun z hz => ?_⟩
      rw [sqz_fix_hi p z (hx.trans hz.1)]
      simp
    push Not at hy hx
    have hx' : 1 / 4 ≤ (x : ℝ) := by
      by_contra h
      push Not at h
      exact h14 ⟨h, hy⟩
    have hy' : (y : ℝ) ≤ 3 / 4 := by
      by_contra h
      push Not at h
      exact h34 ⟨hx, h⟩
    let x' : UI := ⟨2 * (x : ℝ) - 1 / 2, by constructor <;> linarith⟩
    let y' : UI := ⟨2 * (y : ℝ) - 1 / 2, by constructor <;> linarith⟩
    have hxy' : (x' : ℝ) < y' := by
      show 2 * (x : ℝ) - 1 / 2 < 2 * (y : ℝ) - 1 / 2
      linarith
    have hdis' : Set.Ioo (x' : ℝ) y' ∩ (B : Set ℝ) = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨h1, h2⟩, htB⟩
      have h1' : 2 * (x : ℝ) - 1 / 2 < t := h1
      have h2' : t < 2 * (y : ℝ) - 1 / 2 := h2
      have hm : t / 2 + 1 / 4 ∈ Set.Ioo (x : ℝ) y ∩
          ((insert (1 / 4) (insert (3 / 4) (B.image (fun t => t / 2 + 1 / 4))) : Finset ℝ) :
            Set ℝ) :=
        ⟨⟨by linarith, by linarith⟩, Finset.mem_coe.mpr (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ htB)))⟩
      rw [hdis] at hm
      exact hm
    obtain ⟨n, c, hnc⟩ := hB x' y' hxy' hdis'
    refine ⟨n, c / 2 + 1 / 4 - 2 ^ n / 4, fun z hz => ?_⟩
    have hzm : 2 * (z : ℝ) - 1 / 2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have hz' : ((⟨2 * (z : ℝ) - 1 / 2, hzm⟩ : UI) : ℝ) ∈ Set.Icc (x' : ℝ) (y' : ℝ) := by
      show 2 * (z : ℝ) - 1 / 2 ∈ Set.Icc (2 * (x : ℝ) - 1 / 2) (2 * (y : ℝ) - 1 / 2)
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [sqz_coe, extend_apply, extendFun_of_mem p hzm, hnc _ hz']
    ring

/-! ### Unsqueezing a map supported in `[1/4, 3/4]` -/

noncomputable def unsqzL (v : UI ≃o UI) : ℝ ≃o ℝ := sig⁻¹ * extend v * sig

lemma unsqzL_apply (v : UI ≃o UI) (t : ℝ) :
    unsqzL v t = 2 * extend v (t / 2 + 1 / 4) - 1 / 2 := rfl

lemma unsqzL_lo {v : UI ≃o UI} (hv0 : ∀ z : UI, (z : ℝ) ≤ 1 / 4 → (v z : ℝ) = z) :
    ∀ t ≤ (0:ℝ), unsqzL v t = t := by
  intro t ht
  rw [unsqzL_apply, extend_fix_of v _ (fun hs => hv0 ⟨_, hs⟩ (by show t / 2 + 1 / 4 ≤ 1 / 4; linarith))]
  ring

lemma unsqzL_hi {v : UI ≃o UI} (hv1 : ∀ z : UI, 3 / 4 ≤ (z : ℝ) → (v z : ℝ) = z) :
    ∀ t, (1:ℝ) ≤ t → unsqzL v t = t := by
  intro t ht
  rw [unsqzL_apply, extend_fix_of v _ (fun hs => hv1 ⟨_, hs⟩ (by show 3 / 4 ≤ t / 2 + 1 / 4; linarith))]
  ring

lemma isThompson_unsqz {v : UI ≃o UI} (hv : IsThompson v)
    (hv0 : ∀ z : UI, (z : ℝ) ≤ 1 / 4 → (v z : ℝ) = z)
    (hv1 : ∀ z : UI, 3 / 4 ≤ (z : ℝ) → (v z : ℝ) = z) :
    IsThompson (restrict (unsqzL v) (unsqzL_lo hv0) (unsqzL_hi hv1)) := by
  classical
  obtain ⟨B, hBd, hB⟩ := hv
  refine ⟨B.image (fun t => 2 * t - 1 / 2), ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    exact dyadic_sigInv (hBd s hs)
  · intro x y hxy hdis
    have hx0 := x.2.1
    have hy1 := y.2.2
    let x' : UI := ⟨(x : ℝ) / 2 + 1 / 4, by constructor <;> linarith⟩
    let y' : UI := ⟨(y : ℝ) / 2 + 1 / 4, by constructor <;> linarith⟩
    have hxy' : (x' : ℝ) < y' := by
      show (x : ℝ) / 2 + 1 / 4 < (y : ℝ) / 2 + 1 / 4
      linarith
    have hdis' : Set.Ioo (x' : ℝ) y' ∩ (B : Set ℝ) = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Finset.mem_coe, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨⟨h1, h2⟩, htB⟩
      have h1' : (x : ℝ) / 2 + 1 / 4 < t := h1
      have h2' : t < (y : ℝ) / 2 + 1 / 4 := h2
      have hm : 2 * t - 1 / 2 ∈ Set.Ioo (x : ℝ) y ∩
          ((B.image (fun t => 2 * t - 1 / 2) : Finset ℝ) : Set ℝ) :=
        ⟨⟨by linarith, by linarith⟩, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ htB)⟩
      rw [hdis] at hm
      exact hm
    obtain ⟨n, c, hnc⟩ := hB x' y' hxy' hdis'
    refine ⟨n, 2 ^ n / 2 + 2 * c - 1 / 2, fun z hz => ?_⟩
    have hz0 := z.2.1
    have hz1 := z.2.2
    have hzm : (z : ℝ) / 2 + 1 / 4 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hz' : ((⟨(z : ℝ) / 2 + 1 / 4, hzm⟩ : UI) : ℝ) ∈ Set.Icc (x' : ℝ) (y' : ℝ) := by
      show (z : ℝ) / 2 + 1 / 4 ∈ Set.Icc ((x : ℝ) / 2 + 1 / 4) ((y : ℝ) / 2 + 1 / 4)
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [restrict_coe, unsqzL_apply, extend_apply, extendFun_of_mem v hzm, hnc _ hz']
    ring

lemma sqz_unsqz {v : UI ≃o UI}
    (hv0 : ∀ z : UI, (z : ℝ) ≤ 1 / 4 → (v z : ℝ) = z)
    (hv1 : ∀ z : UI, 3 / 4 ≤ (z : ℝ) → (v z : ℝ) = z) :
    sqz (restrict (unsqzL v) (unsqzL_lo hv0) (unsqzL_hi hv1)) = v := by
  refine DFunLike.ext _ _ (fun z => Subtype.ext ?_)
  rw [sqz_coe, extend_restrict, unsqzL_apply]
  have : (2 * (z : ℝ) - 1 / 2) / 2 + 1 / 4 = z := by ring
  rw [this, extend_apply, extendFun_of_mem v z.2]
  ring

end CFPSuppIcc

open CFPSuppIcc in
theorem solution {a b c d : ℝ}
    (ha : 0 < a) (hac : a < c) (hcd : c < d) (hdb : d < b) (hb : b < 1)
    (hda : IsDyadic a) (hdb' : IsDyadic b)
    {u : UI ≃o UI} (hu : u ∈ F) (hsupp : supp u ⊆ Set.Icc c d) :
    u ∈ Subgroup.closure {x : UI ≃o UI | ∃ g h : UI ≃o UI,
      g ∈ F ∧ h ∈ F ∧ supp g ⊆ Set.Icc a b ∧ supp h ⊆ Set.Icc a b ∧ x = g * h * g⁻¹ * h⁻¹} := by
  classical
  have hamem : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha.le, by linarith⟩
  have hbmem : b ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hb.le⟩
  have hcmem : c ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hdmem : d ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hq1 : (1 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hq3 : (3 / 4 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- Step 1: an element `θ ∈ F` with `θ (1/4) = a` and `θ (3/4) = b`.
  obtain ⟨θ, hθF, hθ⟩ := exists_mem_F_map_partition (n := 3)
    ![⟨0, zero_mem_UI⟩, ⟨1 / 4, hq1⟩, ⟨3 / 4, hq3⟩, ⟨1, one_mem_UI⟩]
    ![⟨0, zero_mem_UI⟩, ⟨a, hamem⟩, ⟨b, hbmem⟩, ⟨1, one_mem_UI⟩]
    (Fin.strictMono_iff_lt_succ.mpr (fun i => by
      fin_cases i <;> apply Subtype.coe_lt_coe.mp <;> simp <;> norm_num))
    (Fin.strictMono_iff_lt_succ.mpr (fun i => by
      fin_cases i <;> apply Subtype.coe_lt_coe.mp <;> simp <;> linarith))
    rfl rfl rfl rfl
    (fun i => by
      fin_cases i
      · exact ⟨0, 0, by simp⟩
      · exact ⟨1, 2, by simp; norm_num⟩
      · exact ⟨3, 2, by simp; norm_num⟩
      · exact ⟨1, 0, by simp⟩)
    (fun i => by
      fin_cases i
      · exact ⟨0, 0, by simp⟩
      · simpa using hda
      · simpa using hdb'
      · exact ⟨1, 0, by simp⟩)
  have hθa : θ ⟨1 / 4, hq1⟩ = ⟨a, hamem⟩ := hθ 1
  have hθb : θ ⟨3 / 4, hq3⟩ = ⟨b, hbmem⟩ := hθ 2
  -- Step 2: pull `u` back by `θ`.
  set v : UI ≃o UI := θ⁻¹ * u * θ with hv_def
  have hvF : v ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hθF) hu) hθF
  have hufix : ∀ w : UI, ((w : ℝ) < c ∨ d < (w : ℝ)) → u w = w := by
    intro w hw
    by_contra hne
    have hmem : (w : ℝ) ∈ supp u := ⟨w, rfl, fun h => hne (Subtype.ext h)⟩
    have := hsupp hmem
    rcases hw with h | h
    · linarith [this.1]
    · linarith [this.2]
  set w0 : UI := θ.symm ⟨c, hcmem⟩ with hw0_def
  set w1 : UI := θ.symm ⟨d, hdmem⟩ with hw1_def
  have hw0 : (1 / 4 : ℝ) < (w0 : ℝ) := by
    have : (⟨1 / 4, hq1⟩ : UI) < w0 := by
      rw [hw0_def, OrderIso.lt_symm_apply, hθa]
      exact hac
    exact this
  have hw1 : (w1 : ℝ) < 3 / 4 := by
    have : w1 < (⟨3 / 4, hq3⟩ : UI) := by
      rw [hw1_def, OrderIso.symm_apply_lt, hθb]
      exact hdb
    exact this
  have hv_lo : ∀ z : UI, (z : ℝ) < w0 → (v z : ℝ) = z := by
    intro z hz
    have hz' : z < w0 := hz
    have h1 : θ z < θ w0 := θ.lt_iff_lt.mpr hz'
    rw [hw0_def, θ.apply_symm_apply] at h1
    have h2 : u (θ z) = θ z := hufix _ (Or.inl h1)
    show (θ.symm (u (θ z)) : ℝ) = z
    rw [h2, θ.symm_apply_apply]
  have hv_hi : ∀ z : UI, (w1 : ℝ) < z → (v z : ℝ) = z := by
    intro z hz
    have hz' : w1 < z := hz
    have h1 : θ w1 < θ z := θ.lt_iff_lt.mpr hz'
    rw [hw1_def, θ.apply_symm_apply] at h1
    have h2 : u (θ z) = θ z := hufix _ (Or.inr h1)
    show (θ.symm (u (θ z)) : ℝ) = z
    rw [h2, θ.symm_apply_apply]
  have hv0 : ∀ z : UI, (z : ℝ) ≤ 1 / 4 → (v z : ℝ) = z :=
    fun z hz => hv_lo z (by linarith)
  have hv1 : ∀ z : UI, 3 / 4 ≤ (z : ℝ) → (v z : ℝ) = z :=
    fun z hz => hv_hi z (by linarith)
  -- Step 3: unsqueeze `v` to `g`, trivial near both ends, hence in `[F, F]`.
  set g : UI ≃o UI := restrict (unsqzL v) (unsqzL_lo hv0) (unsqzL_hi hv1) with hg_def
  have hgF : g ∈ F :=
    mem_F_iff_isThompson.mpr (isThompson_unsqz (mem_F_iff_isThompson.mp hvF) hv0 hv1)
  have hg0 : TrivialNearZero g := by
    refine ⟨2 * ((w0 : ℝ) - 1 / 4), by linarith, fun z hz => ?_⟩
    rw [hg_def, restrict_coe, unsqzL_apply,
      extend_fix_of v _ (fun hs => hv_lo ⟨_, hs⟩ (by show (z : ℝ) / 2 + 1 / 4 < w0; linarith))]
    ring
  have hg1 : TrivialNearOne g := by
    refine ⟨2 * (3 / 4 - (w1 : ℝ)), by linarith, fun z hz => ?_⟩
    rw [hg_def, restrict_coe, unsqzL_apply,
      extend_fix_of v _ (fun hs => hv_hi ⟨_, hs⟩ (by show (w1 : ℝ) < (z : ℝ) / 2 + 1 / 4; linarith))]
    ring
  have hgc : (⟨g, hgF⟩ : F) ∈ commutator F := (mem_commutator_iff _).mpr ⟨hg0, hg1⟩
  have hgFF : g ∈ ⁅F, F⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨⟨g, hgF⟩, hgc, rfl⟩
  -- Step 4: transport back by `Θ = θ (sqz ·) θ⁻¹`.
  let Θ : (UI ≃o UI) →* (UI ≃o UI) := (MulAut.conj θ).toMonoidHom.comp sqzHom
  have hΘ : ∀ p, Θ p = θ * sqz p * θ⁻¹ := fun p => rfl
  have hΘg : Θ g = u := by
    rw [hΘ, hg_def, sqz_unsqz hv0 hv1, hv_def]
    group
  have hΘF : ∀ p ∈ F, Θ p ∈ F := by
    intro p hp
    rw [hΘ]
    exact F.mul_mem (F.mul_mem hθF
      (mem_F_of_isThompson (isThompson_sqz (mem_F_iff_isThompson.mp hp)))) (F.inv_mem hθF)
  have hΘsupp : ∀ p, supp (Θ p) ⊆ Set.Icc a b := by
    intro p t ht
    obtain ⟨z, rfl, hne⟩ := ht
    by_contra hout
    apply hne
    rw [Set.mem_Icc, not_and_or] at hout
    have key : sqz p (θ.symm z) = θ.symm z := by
      apply Subtype.ext
      rcases hout with h | h
      · push Not at h
        apply sqz_fix_lo
        have : θ.symm z < ⟨1 / 4, hq1⟩ := by
          rw [OrderIso.symm_apply_lt, hθa]
          exact h
        exact (Subtype.coe_lt_coe.mpr this).le
      · push Not at h
        apply sqz_fix_hi
        have : (⟨3 / 4, hq3⟩ : UI) < θ.symm z := by
          rw [OrderIso.lt_symm_apply, hθb]
          exact h
        exact (Subtype.coe_lt_coe.mpr this).le
    rw [hΘ]
    show (θ (sqz p (θ.symm z)) : ℝ) = z
    rw [key, θ.apply_symm_apply]
  have hmap : u ∈ (⁅F, F⁆).map Θ := ⟨g, hgFF, hΘg⟩
  rw [Subgroup.commutator_def, MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨p, hp, q, hq, rfl⟩, rfl⟩
  refine ⟨Θ p, Θ q, hΘF p hp, hΘF q hq, hΘsupp p, hΘsupp q, ?_⟩
  rw [map_commutatorElement, commutatorElement_def]
