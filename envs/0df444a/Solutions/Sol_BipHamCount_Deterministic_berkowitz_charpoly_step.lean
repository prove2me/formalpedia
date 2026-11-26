-- Prove2me | solution 1 for BipHamCount.Deterministic.berkowitz_charpoly_step
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:12:44.004613+00:00
-- url     : https://prove2.me/submissions/040aeedb-a470-4ff4-a1e6-dda851afc48c

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped PowerSeries Polynomial
open Matrix BigOperators

namespace BerkowitzSeries

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def geom (D : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  fun i j => PowerSeries.mk (fun n => (D ^ n) i j)

noncomputable def pencil (D : Matrix ι ι R) : Matrix ι ι (PowerSeries R) :=
  1 - (PowerSeries.X : PowerSeries R) • (D.map PowerSeries.C)

omit [Fintype ι] in
private lemma coeff_oneMatrix (n : ℕ) (i j : ι) :
    PowerSeries.coeff n ((1 : Matrix ι ι (PowerSeries R)) i j) =
      (if n = 0 then (1 : Matrix ι ι R) i j else 0) := by
  by_cases h : i = j <;> simp [Matrix.one_apply,h,PowerSeries.coeff_one]

private lemma coeff_geom (D : Matrix ι ι R) (n : ℕ) (i j : ι) :
    PowerSeries.coeff n (geom D i j) = (D^n) i j := PowerSeries.coeff_mk _ _

lemma pencil_mul_geom (D : Matrix ι ι R) : pencil D * geom D = 1 := by
  rw [pencil, sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  change PowerSeries.coeff n (geom D i j - PowerSeries.X * (D.map PowerSeries.C * geom D) i j) = _
  rw [map_sub,coeff_geom,coeff_oneMatrix]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,PowerSeries.coeff_succ_X_mul]
    rw [pow_succ']
    simp [Matrix.mul_apply,PowerSeries.coeff_C_mul,coeff_geom]

lemma geom_mul_pencil (D : Matrix ι ι R) : geom D * pencil D = 1 := by
  rw [pencil, mul_sub, mul_one, Matrix.mul_smul]
  ext i j n
  change PowerSeries.coeff n (geom D i j - PowerSeries.X * (geom D * D.map PowerSeries.C) i j) = _
  rw [map_sub,coeff_geom,coeff_oneMatrix]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    simp only [Nat.succ_ne_zero,if_false,PowerSeries.coeff_succ_X_mul]
    rw [pow_succ]
    simp [Matrix.mul_apply,PowerSeries.coeff_mul_C,coeff_geom]

private noncomputable abbrev pencilInvertible (D : Matrix ι ι R) : Invertible (pencil D) :=
  ⟨geom D,geom_mul_pencil D,pencil_mul_geom D⟩


lemma coe_revChar (D : Matrix ι ι R) : (D.charpolyRev : PowerSeries R) = (pencil D).det := by
  change Polynomial.coeToPowerSeries.ringHom D.charpolyRev = _
  rw [Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> (simp [pencil,Matrix.map_apply,h]; exact mul_comm _ _)

noncomputable def seriesQuadratic (b c : ι → R) (D : Matrix ι ι R) : PowerSeries R :=
  ∑ i, ∑ j, PowerSeries.C (b i) * geom D i j * PowerSeries.C (c j)

lemma coeff_seriesQuadratic (b c : ι → R) (D : Matrix ι ι R) (n : ℕ) :
    PowerSeries.coeff n (seriesQuadratic b c D) = ∑ i, ∑ j, b i * (D^n) i j * c j := by
  simp [seriesQuadratic,PowerSeries.coeff_mul_C,PowerSeries.coeff_C_mul,coeff_geom]

lemma berk_block_series (a : R) (b c : ι → R) (D : Matrix ι ι R) :
    ((Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev :
      PowerSeries R) = (D.charpolyRev : PowerSeries R) * (1 - PowerSeries.X * PowerSeries.C a -
      PowerSeries.X ^ 2 * seriesQuadratic b c D) := by
  classical
  let a' : Matrix Unit Unit (PowerSeries R) := fun _ _ => 1 - PowerSeries.X * PowerSeries.C a
  let b' : Matrix Unit ι (PowerSeries R) := fun _ i => -(PowerSeries.X * PowerSeries.C (b i))
  let c' : Matrix ι Unit (PowerSeries R) := fun i _ => -(PowerSeries.X * PowerSeries.C (c i))
  let : Invertible (pencil D) := pencilInvertible D
  have hm : pencil (Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D) =
      Matrix.fromBlocks a' b' c' (pencil D) := by
    ext (i|i) (j|j) <;> simp [pencil,Matrix.one_apply,Matrix.fromBlocks,Matrix.map_apply,a',b',c',Sum.elim]
  rw [coe_revChar,hm,Matrix.det_fromBlocks₂₂,coe_revChar]
  congr 1
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  change 1 - PowerSeries.X * PowerSeries.C a - (b' * geom D * c') () () = _
  congr 1
  change (∑ j, (∑ i, b' () i * geom D i j) * c' j ()) = _
  simp only [Finset.sum_mul,seriesQuadratic,Finset.mul_sum,b',c']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring


/-- The left column of the Berkowitz Toeplitz matrix, continued to all orders. -/
noncomputable def toeplitzCol (a : R) (b c : ι → R) (D : Matrix ι ι R) : ℕ → R
  | 0 => 1
  | 1 => -a
  | k+2 => -(∑ i, ∑ j, b i * (D^k) i j * c j)

private lemma toeplitzCoeff (a : R) (b c : ι → R) (D : Matrix ι ι R) (k : ℕ) :
    PowerSeries.coeff k (1 - PowerSeries.X * PowerSeries.C a -
      PowerSeries.X^2 * seriesQuadratic b c D) = toeplitzCol a b c D k := by
  rw [pow_two,mul_assoc]
  cases k with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff,toeplitzCol]
  | succ k =>
    simp only [map_sub,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_one,Nat.succ_ne_zero,
      if_false,zero_sub]
    cases k with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff,toeplitzCol]
    | succ k => simp [PowerSeries.coeff_succ_X_mul,coeff_seriesQuadratic,toeplitzCol]

theorem berkowitz_recurrence (a : R) (b c : ι → R) (D : Matrix ι ι R) (k : ℕ) :
    ((Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev).coeff k =
      ∑ j ∈ Finset.range (k+1), toeplitzCol a b c D (k-j) * D.charpolyRev.coeff j := by
  rw [← Polynomial.coeff_coe,berk_block_series,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_coe,toeplitzCoeff,mul_comm]

end BerkowitzSeries

theorem solution {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (a : R) (b c : I → R) (D : Matrix I I R) (k : ℕ) :
    let t : ℕ → R
      | 0 => 1
      | 1 => -a
      | l+2 => -(∑ i, ∑ j, b i * (D^l) i j * c j)
    (Matrix.fromBlocks (fun _ _ : Unit => a) (fun _ i => b i) (fun i _ => c i) D).charpolyRev.coeff k =
      ∑ j ∈ Finset.range (k+1), t (k-j) * D.charpolyRev.coeff j := by
  exact BerkowitzSeries.berkowitz_recurrence a b c D k

