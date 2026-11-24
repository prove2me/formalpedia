-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.chi_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:31.96581+00:00
-- url     : https://prove2.me/submissions/d146b70f-9827-448d-8aa5-93c5008abcfc

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Theorems.Thm_Formalism_IndefR_Fin_Four_mk_out_sub
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_Gk_finite
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_out_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option linter.style.haveILetI false
noncomputable section
namespace Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
private theorem chi_nsmul_left_eq_pow {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ (n • s) y = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχl 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 0 y) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]
private theorem chi_nsmul_right_eq_pow {χ : W → W → ℂ} (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ s (n • y) = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχr s 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 s 0) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]
section Uniq
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
end Uniq
section Uniq2
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
end Uniq2
section Uniq3
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
end Uniq3
end Formalism.IndefR.Fin.Four
end
end

set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} (hk : 0 < k) {t : W} (ht : t ∈ L ⊓ X) :
    ∑ᶠ g : Gk L Y k, χ t (g : QY L Y).out =
      if t ∈ smulSub k (L ⊓ X) then (Nat.card (Gk L Y k) : ℂ) else 0 := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hts
  · have h1 : ∀ g : Gk L Y k, χ t (g : QY L Y).out = 1 := by
      intro g
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hts
      have hst' : t = k • s := hst.symm
      obtain ⟨hgY, hgL⟩ := Gk_out g
      rw [hst', chi_nsmul_left_eq_pow hχl hχ0, ← chi_nsmul_right_eq_pow hχr hχ0]
      exact hLL s hs _ (AddSubgroup.mem_inf.mpr ⟨hgL, nsmul_mem hgY k⟩)
    rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  · have hne : ∃ g : Gk L Y k, χ t (g : QY L Y).out ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hts
      have htX : t ∈ X := (AddSubgroup.mem_inf.mp ht).2
      obtain ⟨s, hsX, hks⟩ := hdivX k hk t htX
      have hsL : s ∈ L := by
        apply hdX s hsX
        intro y hy
        obtain ⟨y', hy'Y, hky'⟩ := hdivY k hk y (AddSubgroup.mem_inf.mp hy).2
        have hmem : (QuotientAddGroup.mk y' : QY L Y) ∈ Gk L Y k := by
          refine AddSubgroup.mem_map.mpr ⟨y', AddSubgroup.mem_inf.mpr ⟨hy'Y, ?_⟩, rfl⟩
          show k • y' ∈ L
          rw [hky']
          exact (AddSubgroup.mem_inf.mp hy).1
        have h1 := hall ⟨_, hmem⟩
        obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y'
        have h2 : χ t (QuotientAddGroup.mk y' : QY L Y).out = χ t y' := by
          rw [he, hχr, hLL t ht l hl, mul_one]
        rw [← hky', chi_nsmul_right_eq_pow hχr hχ0, ← chi_nsmul_left_eq_pow hχl hχ0, hks, ← h2]
        exact h1
      exact AddSubgroup.mem_map.mpr ⟨s, AddSubgroup.mem_inf.mpr ⟨hsL, hsX⟩, hks⟩
    obtain ⟨g₀, hg₀⟩ := hne
    have hS : ∑ g : Gk L Y k, χ t (g : QY L Y).out =
        χ t (g₀ : QY L Y).out * ∑ g : Gk L Y k, χ t (g : QY L Y).out := by
      rw [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.addLeft g₀) _ _ (fun g => ?_)
      exact (chi_out_add hχr hLL ht g₀ g).symm
    have h3 : (1 - χ t (g₀ : QY L Y).out) * ∑ g : Gk L Y k, χ t (g : QY L Y).out = 0 := by
      rw [sub_mul, one_mul, ← hS, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hg₀))
end Formalism.IndefR.Fin.Four
