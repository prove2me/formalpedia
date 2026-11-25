-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.theorem_A_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:03.938392+00:00
-- url     : https://prove2.me/submissions/43163db8-d448-4a46-8854-67947343e837

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generic_minor_norm
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_generic_norm_one
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theorem_A_frame
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ThmAGeneric.{u} := by
  intro K _ _ _ l d N0 N1 _ hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I Y hY nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab hJ m hm
  classical
  have hYn : ∀ y, ‖Y y‖ = 1 := generic_norm_one hl Y hY
  have hxg : ∀ y, ‖genFrame TT l m Y y‖ ≤ 1 := by
    intro y
    simp only [genFrame]
    split_ifs <;> simp [norm_pow, hYn]
  have hw : ∀ s (i : Fin (J s)), (lab s i).1 ∈ TT ∧ Odd (lab s i).2 ∧
      s = (lab s i).1 + (((lab s i).2 : ℤ) : ZMod d) := by
    intro s i
    have := (hlab s (lab s i).1 (lab s i).2).mp ⟨i, rfl⟩
    exact ⟨this.1, this.2.1, this.2.2.1⟩
  have hxg0 : ∀ s0 ∈ TT, ∀ a, genFrame TT l m Y (s0, ⟨0, h0⟩, a) = Y (s0, ⟨0, h0⟩, a) ^ l ^ m := by
    intro s0 hs0 a
    simp [genFrame, hs0]
  let E : (s : ZMod d) → Fin (J s) → ℕ := fun s i => ((m : ℤ) + (lab s i).2).toNat
  let lam : (s : ZMod d) → Fin (J s) → Fin N0 → K := fun s i a => Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ E s i
  have hlam1 : ∀ s i a, ‖lam s i a‖ ≤ 1 := by
    intro s i a
    simp [lam, norm_pow, hYn]
  have hpos : ∀ s i a, 0 < (lab s i).2 →
      lam s i a = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) ^ l ^ (lab s i).2.toNat := by
    intro s i a hj
    rw [hxg0 _ (hw s i).1, ← pow_mul, ← pow_add]
    simp only [lam, E]
    congr 2
    omega
  have hneg : ∀ s i a, (lab s i).2 < 0 →
      lam s i a ^ l ^ (-(lab s i).2).toNat = genFrame TT l m Y ((lab s i).1, ⟨0, h0⟩, a) := by
    intro s i a hj
    have hmm := hm s i
    rw [hxg0 _ (hw s i).1]
    simp only [lam, E]
    rw [← pow_mul, ← pow_add]
    congr 2
    omega
  let e : (s : ZMod d) → Fin (J s) → Fin N0 := fun s i =>
    ⟨i + (if s ∈ TT then 1 else 0), by
      have h := hJ s
      have hi := i.isLt
      split_ifs at h ⊢ <;> omega⟩
  have he_inj : ∀ s, Function.Injective (e s) := by
    intro s i i' h
    apply Fin.ext
    have h' := congrArg Fin.val h
    simp only [e] at h'
    omega
  have he0 : ∀ s i, ¬(s ∈ TT ∧ ((e s i : Fin N0) : ℕ) = 0) := by
    intro s i h
    obtain ⟨hs, hz0⟩ := h
    simp [e, hs] at hz0
  have hdet : ∀ s, ‖(Matrix.of fun (i i' : Fin (J s)) =>
      ∑ a : Fin N0, lam s i a * genFrame TT l m Y (s, e s i', a)).det‖ = 1 := by
    intro s
    have hx : ∀ i' a, genFrame TT l m Y (s, e s i', a) = Y (s, e s i', a) := by
      intro i' a
      simp only [genFrame]
      rw [if_neg (he0 s i')]
    simp only [hx]
    have hts : ∀ i, (lab s i).1 ≠ s := by
      intro i h
      obtain ⟨_, hodd, hss⟩ := hw s i
      rw [h] at hss
      have hx0 : (((lab s i).2 : ℤ) : ZMod d) = 0 := by simpa using hss
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx0
      have hev : Even ((d : ℕ) : ℤ) := (Int.even_coe_nat d).mpr he
      obtain ⟨k, hk⟩ := hdvd
      have : Even (lab s i).2 := by
        rw [hk]
        exact hev.mul_right k
      exact (Int.not_even_iff_odd.mpr hodd) this
    have hLn : ∀ i, l ^ E s i ≠ 0 := fun i => pow_ne_zero _ hl.ne_zero
    have hinj' : Function.Injective fun i => ((lab s i).1, l ^ E s i) := by
      intro i i' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨ha1, ha2⟩ := h
      have hE := Nat.pow_right_injective hl.two_le ha2
      simp only [E] at hE
      have hm1 := hm s i
      have hm2 := hm s i'
      have ho1 := (hw s i).2.1
      have ho2 := (hw s i').2.1
      have hn1 : (lab s i).2 ≠ 0 := fun h => by rw [h] at ho1; exact absurd ho1 (by decide)
      have hn2 : (lab s i').2 ≠ 0 := fun h => by rw [h] at ho2; exact absurd ho2 (by decide)
      have hj : (lab s i).2 = (lab s i').2 := by omega
      exact hinj s (Prod.ext ha1 hj)
    have hn : J s ≤ N0 := by
      have h := hJ s
      split_ifs at h <;> omega
    exact generic_minor_norm hl Y hY s ⟨0, h0⟩ (fun i => (lab s i).1) (fun i => l ^ E s i) (e s)
      (he_inj s) hn hts hLn hinj'
  exact theorem_A_frame K l d N0 N1 hl h3 h2 he hlt h0 K0 hu ζ hz be hb g hg0 hgi U hU ε hε TT colN p hp hp1 I
    (genFrame TT l m Y) hxg nu1 nu2 size h1 h2' h3' a ha hs J lab hinj hlab lam hlam1 hpos hneg e he_inj he0 hdet
end Formalism.DworkPowerSeriesWeights
