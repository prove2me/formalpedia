-- Prove2me | solution 1 for GJKKL.Main.Regime.card_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:29.545748+00:00
-- url     : https://prove2.me/submissions/6243ec61-6c46-42a6-bd54-c4bc8e7e31f2

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_d_split
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_Regime_rp_pos
public import Theorems.Thm_GJKKL_mul_degree_le
public import Theorems.Thm_P2M_GJKKL_Main_Regime_dneg__le_half_813c5920422f


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
namespace GJKKL.Main.Regime
theorem _root_.solution (hunif : IsUniform H k)
    (hmin : ∀ v : V, (1 - d ^ (-ε)) * d ≤ (degree H v : ℝ))
    (hcod : ∀ u w : V, u ≠ w → (codegree H u w : ℝ) ≤ d ^ (1 - ε)) (v : V) :
    ((k : ℝ) - 1) * d ^ ε / 2 ≤ Fintype.card V := by
  have hc : ∀ u w, u ≠ w → codegree H u w ≤ ⌊d ^ (1 - ε)⌋₊ :=
    fun u w h => Nat.le_floor (hcod u w h)
  have hmul := mul_degree_le H hunif hc v
  have hcR : (⌊d ^ (1 - ε)⌋₊ : ℝ) ≤ d ^ (1 - ε) := Nat.floor_le (R.rp_pos _).le
  have hcard : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  have hk1 : 1 ≤ k := by have := R.two_le; omega
  have hmulR : ((k : ℝ) - 1) * degree H v ≤ ((Fintype.card V : ℝ) - 1) * ⌊d ^ (1 - ε)⌋₊ := by
    have := (Nat.cast_le (α := ℝ)).mpr hmul
    push_cast [Nat.cast_sub hk1, Nat.cast_sub hcard] at this
    exact this
  have hdeg : d / 2 ≤ (degree H v : ℝ) := by
    have := hmin v
    have h := R.dnegε_le_half
    nlinarith [R.d_pos]
  have hk1R : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith [R.k_ge]
  have h1 : ((k : ℝ) - 1) * (d / 2) ≤ (Fintype.card V : ℝ) * d ^ (1 - ε) := by
    calc ((k : ℝ) - 1) * (d / 2) ≤ ((k : ℝ) - 1) * degree H v :=
          mul_le_mul_of_nonneg_left hdeg hk1R
      _ ≤ ((Fintype.card V : ℝ) - 1) * ⌊d ^ (1 - ε)⌋₊ := hmulR
      _ ≤ (Fintype.card V : ℝ) * d ^ (1 - ε) := by
          have h0 : (0 : ℝ) ≤ ⌊d ^ (1 - ε)⌋₊ := Nat.cast_nonneg _
          have hc1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
          nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 (R.rp_pos ε).le
  have e1 : ((k : ℝ) - 1) * (d / 2) * d ^ ε = ((k : ℝ) - 1) * d ^ ε / 2 * d := by ring
  have e2 : (Fintype.card V : ℝ) * d ^ (1 - ε) * d ^ ε = Fintype.card V * d := by
    rw [mul_assoc, R.d_split]
  rw [e1, e2] at h2
  exact le_of_mul_le_mul_right h2 R.d_pos
end GJKKL.Main.Regime
