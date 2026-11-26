-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerNaturalDensityAtLeast_targetHeightFailure_fixedPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:45.163528+00:00
-- url     : https://prove2.me/submissions/50eefc32-ed96-46e6-a56b-e78cd288d3d8

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_targetHeightFailureCount_ge_periodicBlock
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {h : ℕ} {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ᶠ n : ℕ in Filter.atTop,
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    LowerNaturalDensityAtLeast (targetHeightFailureSet f u)
      ((multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h) := by
  intro d hd
  obtain ⟨N₀, hN₀⟩ := (Filter.eventually_atTop.1 htarget)
  let N := max 1 N₀
  let q := 2 ^ h
  let a := multiplicativeHitCount u h 1
  have hN : 1 ≤ N := le_max_left _ _
  have htargetN : ∀ n : ℕ, N ≤ n →
      f n < (n : ℝ) / (2 : ℝ) ^ h := by
    intro n hn
    exact hN₀ n ((le_max_right 1 N₀).trans hn)
  have hqPos : 0 < q := by dsimp [q]; positivity
  have hgap : 0 < (a : ℝ) / (q : ℝ) - d := by
    have hd' : d < (a : ℝ) / (q : ℝ) := by
      simpa [a, q] using hd
    linarith
  let threshold : ℝ :=
    max (((N + 1) * q : ℕ) : ℝ)
      (2 * (((N + 1) * a : ℕ) : ℝ) /
        ((a : ℝ) / (q : ℝ) - d))
  obtain ⟨X₀ : ℕ, hX₀⟩ := exists_nat_gt threshold
  refine Filter.eventually_atTop.2 ⟨X₀, ?_⟩
  intro X hX
  have hXR : threshold < (X : ℝ) :=
    hX₀.trans_le (by exact_mod_cast hX)
  have hXblockR : (((N + 1) * q : ℕ) : ℝ) < X :=
    (le_max_left _ _).trans_lt hXR
  have hXblock : (N + 1) * q ≤ X := by
    exact_mod_cast hXblockR.le
  have hXposNat : 0 < X :=
    (Nat.mul_pos (by omega) hqPos).trans_le hXblock
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  let t := X / q
  have hNt : N + 1 ≤ t := by
    dsimp [t]
    exact (Nat.le_div_iff_mul_le hqPos).2 hXblock
  have htN : N ≤ t := by omega
  have htqX : t * 2 ^ h ≤ X := by
    dsimp [t, q] at *
    exact Nat.div_mul_le_self X (2 ^ h)
  have hcountNat := targetHeightFailureCount_ge_periodicBlock
    (u := u) hN htqX htargetN
  have hcount :
      (((t - N) * a : ℕ) : ℝ) ≤
        targetHeightFailureCount f u X := by
    dsimp [a]
    exact_mod_cast hcountNat
  have hcount' :
      ((t : ℝ) - (N : ℝ)) * (a : ℝ) ≤
        (targetHeightFailureCount f u X : ℝ) := by
    rw [← Nat.cast_sub htN, ← Nat.cast_mul]
    exact hcount
  have hxltNat : X < (t + 1) * q := by
    dsimp [t]
    calc
      X < X / q * q + q := Nat.lt_div_mul_add hqPos
      _ = (X / q + 1) * q := by ring
  have hxlt : (X : ℝ) < ((t : ℝ) + 1) * (q : ℝ) := by
    exact_mod_cast hxltNat
  have htailR :
      2 * (((N + 1) * a : ℕ) : ℝ) /
          ((a : ℝ) / (q : ℝ) - d) < X :=
    (le_max_right _ _).trans_lt hXR
  have htail :
      (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) <
        ((a : ℝ) / (q : ℝ) - d) / 2 := by
    apply (div_lt_div_iff₀ hXpos (by norm_num : (0 : ℝ) < 2)).2
    have hmul := (div_lt_iff₀ hgap).1 htailR
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hperiodic :
      (a : ℝ) / (q : ℝ) -
          (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) ≤
        ((t : ℝ) - (N : ℝ)) * (a : ℝ) / (X : ℝ) := by
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hqPos
    have ha : 0 ≤ (a : ℝ) := by positivity
    have hxdiv : (X : ℝ) / (q : ℝ) ≤ (t : ℝ) + 1 :=
      (div_le_iff₀ hqR).2 hxlt.le
    have hamul :
        (a : ℝ) * ((X : ℝ) / (q : ℝ)) ≤
          (a : ℝ) * ((t : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hxdiv ha
    apply (le_div_iff₀ hXpos).2
    calc
      ((a : ℝ) / (q : ℝ) -
          (((N + 1) * a : ℕ) : ℝ) / (X : ℝ)) * (X : ℝ) =
          (a : ℝ) * ((X : ℝ) / (q : ℝ)) -
            (((N + 1) * a : ℕ) : ℝ) := by field_simp
      _ ≤ (a : ℝ) * ((t : ℝ) + 1) -
            (((N + 1) * a : ℕ) : ℝ) :=
        sub_le_sub_right hamul _
      _ = ((t : ℝ) - (N : ℝ)) * (a : ℝ) := by
        push_cast
        ring
  have hdPeriodic :
      d < (a : ℝ) / (q : ℝ) -
        (((N + 1) * a : ℕ) : ℝ) / (X : ℝ) := by
    linarith
  have hratio :
      ((t : ℝ) - (N : ℝ)) * (a : ℝ) / (X : ℝ) ≤
        (targetHeightFailureCount f u X : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right hcount' hXpos.le
  have hresult :
      d ≤ (targetHeightFailureCount f u X : ℝ) / (X : ℝ) :=
    hdPeriodic.le.trans (hperiodic.trans hratio)
  change d ≤ (targetHeightFailureCount f u X : ℝ) / (X : ℝ)
  exact hresult
end FirstPassageLinearTransport
