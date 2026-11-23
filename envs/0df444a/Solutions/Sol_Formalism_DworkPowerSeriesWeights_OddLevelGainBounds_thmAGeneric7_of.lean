-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.thmAGeneric7_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:58.717934+00:00
-- url     : https://prove2.me/submissions/8438c951-938f-4520-81f8-24227f752581

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementF
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_ThmAGeneric7Of
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generic_minor_norm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generic_norm_one
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
theorem _root_.solution : ThmAFrame7.{u} → ThmAGeneric7.{u} := by
  intro hFrame K _ _ _ l d N0 N1 _ hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I
    Y hY nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab hJ m hm
  classical
  have hY1 : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hl2 : 2 ≤ l := hl.two_le

  have hprop : ∀ s i, (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧ s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) :=
    fun s i => by
      have := (hlab s (lab s i).1 (lab s i).2).1 ⟨i, rfl⟩
      exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hge : ∀ s i, 0 ≤ (m : ℤ) + (lab s i).2 := fun s i => by
    have := hm s i
    omega
  have hne : ∀ s i, (lab s i).1 ≠ s := by
    intro s i h
    obtain ⟨-, hodd, hs⟩ := hprop s i
    rw [h] at hs
    have hz : (((lab s i).2 : ℤ) : ZMod d) = 0 := by
      have := hs.symm
      rwa [add_eq_left] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    have h2 : (2 : ℤ) ∣ (lab s i).2 := dvd_trans (by exact_mod_cast hev.two_dvd) hz
    exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  have htop : ∀ s i b, genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, b) =
      Y ((lab s i).1, ⟨0, h0⟩, b) ^ (l ^ m) := fun s i b => by
    unfold genFrame
    rw [if_pos ⟨(hprop s i).1, rfl⟩]
  let Lx : ∀ s, Fin (J s) → ℕ := fun s i => l ^ ((m : ℤ) + (lab s i).2).toNat
  let e : ∀ s, Fin (J s) → Fin N0 := fun s i =>
    ⟨i.val + (if s ∈ TT then 1 else 0), lt_of_lt_of_le (by have := i.isLt; omega) (hJ s)⟩
  have hetop : ∀ s i, ¬ (s ∈ TT ∧ (e s i).val = 0) := by
    rintro s i ⟨hs, h⟩
    simp only [e, if_pos hs] at h
    omega
  refine hFrame K l d N0 N1 hl hl3 hd hev hlK h0 K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p
    hp hp1 I (genFrame TT l m Y) ?_ nu1 nu2 size hnu1 hnu2 hsize J lab hlabinj hlab
    (fun s i b => Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i)) ?_ ?_ ?_ e ?_ hetop ?_
  · intro y
    simp only [genFrame]
    split_ifs
    · rw [norm_pow, hY1, one_pow]
    · rw [hY1]
  · intro s i b
    simp only [norm_pow, hY1, one_pow, le_refl]
  · intro s i b hpos
    rw [htop, ← pow_mul, ← pow_add]
    have hx : ((m : ℤ) + (lab s i).2).toNat = m + (lab s i).2.toNat := by omega
    simp only [Lx, hx]
  · intro s i b hneg
    have hx : ((m : ℤ) + (lab s i).2).toNat + (-(lab s i).2).toNat = m := by
      have := hge s i
      omega
    simp only [Lx]
    rw [htop, ← pow_mul, ← pow_add, hx]
  · intro s i i' h
    have := congrArg Fin.val h
    simp only [e] at this
    exact Fin.ext (by omega)
  · intro s
    have hmat : (Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) *
          genFrame TT l m Y (s, e s i', b)) =
        Matrix.of fun (i i' : Fin (J s)) => ∑ b, Y ((lab s i).1, ⟨0, h0⟩, b) ^ (Lx s i) *
          Y (s, e s i', b) := by
      ext i i'
      simp only [Matrix.of_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [genFrame]
      rw [if_neg (hetop s i')]
    rw [hmat]
    refine generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (Lx s) (e s) ?_ ?_ (hne s) ?_ ?_
    · intro i i' h
      have := congrArg Fin.val h
      simp only [e] at this
      exact Fin.ext (by omega)
    · have := hJ s
      omega
    · intro i
      exact pow_ne_zero _ (by omega)
    · intro i i' h
      simp only [Prod.mk.injEq, Lx] at h
      have h2 := Nat.pow_right_injective hl2 h.2
      have := hge s i
      have := hge s i'
      exact hlabinj s (Prod.ext h.1 (by omega))
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
