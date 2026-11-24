-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_tunedIdeal_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:26.048925+00:00
-- url     : https://prove2.me/submissions/321ef091-d095-412b-9a30-387dfa180dca

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_eq_sum
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_eq_prod
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_eq_iSup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_iSup_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mul_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_pow_succ_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
section
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
private theorem mul_sup_le {R : Type*} [CommRing R] (B X Y T : Ideal R)
    (hX : B * X ≤ T) (hY : B * Y ≤ T) : B * (X ⊔ Y) ≤ T := by
  refine Ideal.mul_le.mpr ?_
  intro b hb z hz
  rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
  rw [mul_add]
  exact Submodule.add_mem T (hX (Ideal.mul_mem_mul hb hx)) (hY (Ideal.mul_mem_mul hb hy))
private theorem derivIdeal_one {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] : derivIdeal A (1 : Ideal R) = 1 := by
  rw [Ideal.one_eq_top]
  exact derivIdeal_top A
private theorem tuningWeight_eq_add_sub_of_succ (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) :
    tuningWeight m c = tuningWeight m d + (m - i) := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyc : tuningWeight m c
      = (m - i) * c i + ∑ j ∈ (Finset.range m).erase i, (m - j) * c j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * c j) hmem).symm
  have keyd : tuningWeight m d
      = (m - i) * d i + ∑ j ∈ (Finset.range m).erase i, (m - j) * d j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * d j) hmem).symm
  have h3 : ∑ j ∈ (Finset.range m).erase i, (m - j) * d j
      = ∑ j ∈ (Finset.range m).erase i, (m - j) * c j :=
    Finset.sum_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyc, keyd, h3, ← hdi]
  ring
private theorem tuningMonomial_eq_derivIdealIterate_mul_of_succ {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J : Ideal R) (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i = c i + 1) :
    tuningMonomial A J m d = derivIdealIterate A i J * tuningMonomial A J m c := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyd : tuningMonomial A J m d
      = derivIdealIterate A i J ^ d i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ d j) hmem).symm
  have keyc : tuningMonomial A J m c
      = derivIdealIterate A i J ^ c i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ c j) hmem).symm
  have h3 : ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j
      = ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j :=
    Finset.prod_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyd, keyc, h3, hdi, pow_succ]
  simp only [mul_comm, mul_assoc]
private theorem derivIdealIterate_succ_mul_tuningMonomial_le {A : Type*} [CommRing A] {R : Type*}
    [CommRing R] [Algebra A R] (J : Ideal R) (m s i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) (hc : s + 1 ≤ tuningWeight m c) :
    derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tunedIdeal A J m s := by
  have hw : tuningWeight m c = tuningWeight m d + (m - i) :=
    tuningWeight_eq_add_sub_of_succ m i hi c d hne hdi
  rcases Nat.lt_or_ge (i + 1) m with hlt | hge
  · have hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j)
        = derivIdealIterate A (i + 1) J * tuningMonomial A J m d :=
      tuningMonomial_eq_derivIdealIterate_mul_of_succ J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j)
        (fun j hj => by simp [hj]) (by simp)
    have hw' : tuningWeight m (fun j => if j = i + 1 then d j + 1 else d j)
        = tuningWeight m d + (m - (i + 1)) :=
      tuningWeight_eq_add_sub_of_succ m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d
        (fun j hj => by simp [hj]) (by simp)
    refine le_trans (le_of_eq hmono.symm)
      (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)
    omega
  · have hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d :=
      Ideal.mul_le.mpr fun r _ t ht => Ideal.mul_mem_left _ r ht
    refine le_trans hle (tuningMonomial_le_tunedIdeal A J m s d ?_)
    omega
private theorem mul_derivIdeal_prod_le {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J T : Ideal R) (c : ℕ → ℕ) :
    ∀ (n : ℕ) (B : Ideal R),
      B * (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T →
      (∀ i, i < n → ∀ d : ℕ → ℕ, (∀ j, j ≠ i → d j = c j) → d i + 1 = c i →
        B * (derivIdealIterate A (i + 1) J *
          ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ d j) ≤ T) →
      B * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T := by
  intro n
  induction n with
  | zero =>
      intro B h1 _
      rw [Finset.range_zero, Finset.prod_empty, derivIdeal_one, mul_one]
      rw [Finset.range_zero, Finset.prod_empty, mul_one] at h1
      exact h1
  | succ n ih =>
      intro B h1 h2
      rw [Finset.prod_range_succ] at h1
      rw [Finset.prod_range_succ]
      refine le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_
      refine mul_sup_le B _ _ T ?_ ?_
      · rcases Nat.eq_zero_or_pos (c n) with h0 | hpos
        · rw [h0, pow_zero, mul_one] at h1
          rw [h0, pow_zero, derivIdeal_one, mul_one]
          exact h1
        · obtain ⟨e, he⟩ : ∃ e, c n = e + 1 := ⟨c n - 1, by omega⟩
          have hq1 : (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ (if j = n then e else c j))
              = ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j :=
            Finset.prod_congr rfl fun j hj => by
              rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
          have hq2 : derivIdealIterate A n J ^ (if n = n then e else c n)
              = derivIdealIterate A n J ^ e := by simp
          have hprod : (∏ j ∈ Finset.range (n + 1),
                derivIdealIterate A j J ^ (if j = n then e else c j))
              = (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e := by
            rw [Finset.prod_range_succ, hq1, hq2]
          have hd : B * (derivIdealIterate A (n + 1) J *
              ((∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e)) ≤ T := by
            rw [← hprod]
            exact h2 n (Nat.lt_succ_self n) (fun j => if j = n then e else c j)
              (fun j hj => by simp [hj]) (by simp [he])
          have hstep : derivIdeal A (derivIdealIterate A n J ^ c n)
              ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J := by
            rw [he, derivIdealIterate_succ]
            exact derivIdeal_pow_succ_le A (derivIdealIterate A n J) e
          refine le_trans (Ideal.mul_mono le_rfl (Ideal.mul_mono le_rfl hstep)) ?_
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]
      · have heq : B * (derivIdealIterate A n J ^ c n *
            derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j))
            = (B * derivIdealIterate A n J ^ c n) *
              derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) :=
          (mul_assoc _ _ _).symm
        rw [heq]
        refine ih (B * derivIdealIterate A n J ^ c n) ?_ ?_
        · refine le_trans (le_of_eq ?_) h1
          simp only [mul_comm, mul_assoc]
        · intro i hi d hne hdi
          have hd := h2 i (Nat.lt_succ_of_lt hi) d hne hdi
          rw [Finset.prod_range_succ, hne n (by omega : n ≠ i)] at hd
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]
section
variable [Algebra ℚ S]
end
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (J : Ideal S) (m s : ℕ) :
    derivIdeal k (tunedIdeal k J m (s + 1)) ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_eq_iSup k J m (s + 1)]
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro c
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro hc
  rw [tuningMonomial_eq_prod]
  refine le_trans (le_of_eq (one_mul _).symm) ?_
  refine mul_derivIdeal_prod_le J (tunedIdeal k J m s) c m 1 ?_ ?_
  · rw [one_mul]
    exact tuningMonomial_le_tunedIdeal k J m s c (by omega)
  · intro i hi d hne hdi
    rw [one_mul]
    exact derivIdealIterate_succ_mul_tuningMonomial_le J m s i hi c d hne hdi hc
end FunctorialResolution.EmbeddedResolution
