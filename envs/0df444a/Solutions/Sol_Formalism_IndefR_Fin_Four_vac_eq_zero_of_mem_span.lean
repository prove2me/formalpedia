-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.vac_eq_zero_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:44.521665+00:00
-- url     : https://prove2.me/submissions/49c508bd-c040-4dfc-9fa6-a00613dc075c

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
import Theorems.Thm_Formalism_IndefR_Fin_Four_Ik_finite
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsLev_mul
import Theorems.Thm_Formalism_IndefR_Fin_Four_piK_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_piK_smul
import Theorems.Thm_Formalism_IndefR_Fin_Four_piK_sub
import Theorems.Thm_Formalism_IndefR_Fin_Four_piK_shift
import Theorems.Thm_Formalism_IndefR_Fin_Four_piK_vac
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hY hXY hχl hχr hχ0 hLL hdY hfinX hfinY htf
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L) (Θ : Set V)
    (hlev : ∀ G ∈ Θ, ∃ k : ℕ, 0 < k ∧ IsLev ρ L X Y k G) {w : V}
    (hwX : ∀ u ∈ L ⊓ X, ρ u w = w) (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w)
    (hw : w ∈ Submodule.span ℂ {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : w = 0 := by
  classical
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hw
  choose u hu G hG hg using fun i => (g i).2
  choose kf hkf0 hkf using fun i => hlev (G i) (hG i)
  choose mf hmf0 hmf using fun i => hoY (u i) (hu i)
  set K := ∏ i, (kf i * mf i) with hKdef
  have hK0 : 0 < K := Finset.prod_pos fun i _ => Nat.mul_pos (hkf0 i) (hmf0 i)
  have hdiv : ∀ i, kf i * mf i ∣ K := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  haveI := hfinX K hK0
  haveI := hfinY (K * K) (Nat.mul_pos hK0 hK0)
  haveI : Finite (Ik L Y K) := Ik_finite (htf K hK0)
  have hzero : ∀ i, piK ρ L X Y K (ρ (u i) (G i) - G i) = 0 := by
    intro i
    obtain ⟨c, hc⟩ := hdiv i
    have hGK : IsLev ρ L X Y K (G i) := by
      have := (hkf i).mul (mf i * c)
      rwa [← mul_assoc, ← hc] at this
    have huK : u i ∈ Yk L Y K := mem_Yk.2 ⟨hu i, by
      rw [hc, mul_comm (kf i) (mf i), mul_assoc, mul_comm, ← smul_smul]
      exact L.nsmul_mem (hmf i) _⟩
    rw [piK_sub, piK_shift hY huK hGK.2, sub_self]
  have hpw : piK ρ L X Y K w = 0 := by
    rw [← hsum]
    have : ∀ s : Finset (Fin n), piK ρ L X Y K (∑ i ∈ s, f i • ((g i : {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : V)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        have := piK_smul (ρ := ρ) (L := L) (X := X) (Y := Y) (k := K) (0 : ℂ) (0 : V)
        rwa [zero_smul, zero_smul] at this
      | insert i s his ih =>
        rw [Finset.sum_insert his, piK_add, ih, add_zero, piK_smul, hg i, hzero i, smul_zero]
    exact this Finset.univ
  obtain ⟨c, hc0, hc⟩ := piK_vac hXY hχl hχr hχ0 hLL hdY (k := K) hwX hwY
  rw [hc] at hpw
  exact (smul_eq_zero.1 hpw).resolve_left hc0
end Formalism.IndefR.Fin.Four
