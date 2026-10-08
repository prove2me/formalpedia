-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.fock_hamiltonian_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:00:36.225814+00:00
-- url     : https://prove2.me/submissions/2a79b85e-d4b8-469b-91a6-3352508429a1

import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.DirectSumEsa
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow.FockCanonical

open scoped ENNReal

open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

set_option autoImplicit false

variable {d : ℕ} {κ : Fin d → ℝ}

theorem s61074160_ann_coord (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((ann i x : lpFiniteModes (Occ d)) : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) α
      = (Real.sqrt ((α i : ℝ) + 1) : ℂ) * ((x : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) (up i α) :=
  rfl

theorem s61074160_cre_coord (i : Fin d) (x : lpFiniteModes (Occ d)) (α : Occ d) :
    (((cre i x : lpFiniteModes (Occ d)) : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) α
      = (Real.sqrt (α i : ℝ) : ℂ) * ((x : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) (dn i α) :=
  rfl

theorem s61074160_lhs_coord (i : Fin d) (x : lpFiniteModes (Occ d)) (β : Occ d) :
    ((((((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i))) x
        : lpFiniteModes (Occ d)) : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) β
      = Complex.I * ((Real.sqrt (κ i / 2) : ℂ) * (Real.sqrt (κ i / 2) : ℂ)) *
        ((Real.sqrt (β i : ℝ) : ℂ) * ((Real.sqrt ((dn i β) i : ℝ) : ℂ) *
            ((x : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) (dn i (dn i β)))
          - (Real.sqrt ((β i : ℝ) + 1) : ℂ) * ((Real.sqrt (((up i β) i : ℝ) + 1) : ℂ) *
            ((x : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) (up i (up i β)))) := by
  simp only [FockCanonical.mom, FockCanonical.drift, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sub_apply, map_smul, map_add, map_sub, Submodule.coe_smul, Submodule.coe_add,
    Submodule.coe_sub, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul, s61074160_ann_coord, s61074160_cre_coord]
  ring

theorem s61074160_probe (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (x : lpFiniteModes (Occ d)) (β : Occ d) :
    ((ShiftData.shiftH (modeData hκ i) (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ)) x)
      : L2I (Occ d)) : Occ d → ℂ) β
      = (modeData hκ i).hFun ((x : lp (fun _ : Occ d => ℂ) 2) : Occ d → ℂ) β := rfl

theorem s61074160_up_up (i : Fin d) (β : Occ d) : up i (up i β) = modeShift i β := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [FockCanonical.up, modeShift]
  · simp [FockCanonical.up, modeShift, Function.update_of_ne hj]

theorem s61074160_key (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) (X : Occ d → ℂ) (β : Occ d) :
    Complex.I * ((κ i / 2 : ℝ) : ℂ) *
        ((Real.sqrt (β i : ℝ) : ℂ) * ((Real.sqrt ((dn i β) i : ℝ) : ℂ) * X (dn i (dn i β)))
          - (Real.sqrt ((β i : ℝ) + 1) : ℂ) * ((Real.sqrt (((up i β) i : ℝ) + 1) : ℂ) *
            X (up i (up i β))))
      = (modeData hκ i).hFun X β := by
  have hamp : (modeData hκ i).amp = modeAmp κ i := rfl
  have hsh : (modeData hκ i).shift = modeShift i := rfl
  have hupi : ((up i β i : ℕ) : ℝ) + 1 = (β i : ℝ) + 2 := by
    simp [FockCanonical.up]; ring
  have hB : (Real.sqrt ((β i : ℝ) + 1) : ℂ) * (Real.sqrt (((up i β) i : ℝ) + 1) : ℂ)
      = ((Real.sqrt (((β i : ℝ) + 1) * ((β i : ℝ) + 2)) : ℝ) : ℂ) := by
    rw [hupi, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  have hR2 : (modeData hκ i).amp β * X ((modeData hκ i).shift β)
      = (modeAmp κ i β : ℂ) * X (up i (up i β)) := by
    rw [hamp, hsh, s61074160_up_up]
  simp only [ShiftData.hFun]
  by_cases hb : 2 ≤ β i
  · have hex : modeShift i (Function.update β i (β i - 2)) = β := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [modeShift]
        omega
      · simp [modeShift, Function.update_of_ne hj]
    obtain ⟨α, rfl⟩ : ∃ α, modeShift i α = β := ⟨_, hex⟩
    have hh : (modeData hκ i).hop (fun γ => ((modeData hκ i).amp γ : ℂ) * X γ) (modeShift i α)
        = ((modeAmp κ i α : ℝ) : ℂ) * X α := ShiftData.hop_shift (modeData hκ i) _ α
    have hdd : dn i (dn i (modeShift i α)) = α := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [FockCanonical.dn, modeShift]
      · simp [FockCanonical.dn, modeShift, Function.update_of_ne hj]
    have hA : (Real.sqrt (modeShift i α i : ℝ) : ℂ) * (Real.sqrt ((dn i (modeShift i α)) i : ℝ) : ℂ)
        = ((Real.sqrt (((α i : ℝ) + 1) * ((α i : ℝ) + 2)) : ℝ) : ℂ) := by
      have h1 : ((modeShift i α i : ℕ) : ℝ) = (α i : ℝ) + 2 := by simp
      have h2 : (((dn i (modeShift i α)) i : ℕ) : ℝ) = (α i : ℝ) + 1 := by
        simp [FockCanonical.dn, modeShift]
      rw [h1, h2, Real.sqrt_mul (by positivity), Complex.ofReal_mul, mul_comm]
    rw [hh, hR2, hdd]
    rw [← mul_assoc (Real.sqrt (modeShift i α i : ℝ) : ℂ), hA, ← mul_assoc _ _ (X (up i _)), hB]
    simp only [modeAmp]
    push_cast
    ring
  · have hno : ¬ ∃ α, (modeData hκ i).shift α = β := by
      rintro ⟨α, hα⟩
      apply hb
      rw [← hα, hsh]
      simp
    rw [ShiftData.hop_eq_zero (modeData hκ i) _ hno, hR2]
    have hA : (Real.sqrt (β i : ℝ) : ℂ) * (Real.sqrt ((dn i β) i : ℝ) : ℂ) = 0 := by
      rcases (show β i = 0 ∨ β i = 1 by omega) with h | h
      · simp [h]
      · simp [FockCanonical.dn, h]
    rw [← mul_assoc (Real.sqrt (β i : ℝ) : ℂ), hA, ← mul_assoc _ _ (X (up i _)), hB]
    simp only [modeAmp]
    push_cast
    ring

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockCanonical BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.IkebeKato in
theorem s61074160_mode {d : ℕ} {κ : Fin d → ℝ} (hκ : ∀ i, 0 ≤ κ i) (i : Fin d) :
    (lpFiniteModes (Occ d)).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))
      = (ShiftData.shiftH (modeData hκ i)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by
  refine LinearMap.ext fun x => lp.ext (funext fun β => ?_)
  have hc : ((Real.sqrt (κ i / 2) : ℝ) : ℂ) * ((Real.sqrt (κ i / 2) : ℝ) : ℂ)
      = ((κ i / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith [hκ i])]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [s61074160_lhs_coord, hc]
  exact (s61074160_key hκ i _ β).trans (s61074160_probe hκ i x β).symm

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockCanonical BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.FockManyMode BookProof.NavierStokesFlow.IkebeKato in
theorem solution {d : ℕ} {κ : Fin d → ℝ} (hκ : ∀ i, 0 ≤ κ i) :
    (lpFiniteModes (Occ d)).subtype.comp
        (∑ i, ((1 : ℂ) / 2) • ((mom κ i).comp (drift κ i) + (drift κ i).comp (mom κ i)))
      = (fockH hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (fockSym κ))) := by
  refine LinearMap.ext fun x => ?_
  have h2 : ∀ y : maxDom (fockSym κ),
      FockManyMode.fockH hκ y = ∑ i, ShiftData.shiftH (modeData hκ i) y :=
    fun y => LinearMap.sum_apply _ _ _
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h2, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (s61074160_mode hκ i) x
