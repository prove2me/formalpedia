-- Prove2me | solution 1 for EconomicsNextProof.upperMobius_upperSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:54.015739+00:00
-- url     : https://prove2.me/submissions/416e808c-9488-4ff0-b945-e3283ead3e8e

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Theorems.Thm_EconomicsNextProof_alternating_interval
section
@[expose] public section
namespace EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
private lemma booleanMu_eq_mu :
    (booleanMu : IncidenceAlgebra ℝ (Finset X)) = IncidenceAlgebra.mu ℝ := by
  have h : (booleanMu : IncidenceAlgebra ℝ (Finset X)) *
      IncidenceAlgebra.zeta ℝ = 1 := by
    apply IncidenceAlgebra.ext
    intro A C hAC
    rw [IncidenceAlgebra.mul_apply]
    calc
      ∑ B ∈ Finset.Icc A C, booleanMu A B * IncidenceAlgebra.zeta ℝ B C
          = ∑ B ∈ Finset.Icc A C, (-1 : ℝ) ^ (B \ A).card := by
              apply Finset.sum_congr rfl
              intro B hB
              have hb := Finset.mem_Icc.mp hB
              simp [booleanMu, IncidenceAlgebra.zeta_apply, hb.1, hb.2]
      _ = (1 : IncidenceAlgebra ℝ (Finset X)) A C := by
        rw [alternating_interval A C hAC, IncidenceAlgebra.one_apply]
  calc
    booleanMu = booleanMu * (IncidenceAlgebra.zeta ℝ * IncidenceAlgebra.mu ℝ) := by
      rw [IncidenceAlgebra.zeta_mul_mu, mul_one]
    _ = (booleanMu * IncidenceAlgebra.zeta ℝ) * IncidenceAlgebra.mu ℝ := by rw [mul_assoc]
    _ = IncidenceAlgebra.mu ℝ := by rw [h, one_mul]
private lemma upperSum_eq_Ici (f : Finset X → ℝ) (A : Finset X) :
    upperSum f A = ∑ B ∈ Finset.Ici A, f B := by
  unfold upperSum
  congr 1
  ext B
  simp
private lemma upperMobius_eq_mu (f : Finset X → ℝ) (A : Finset X) :
    upperMobius f A = ∑ B ∈ Finset.Ici A, IncidenceAlgebra.mu ℝ A B * f B := by
  have hs : Finset.univ.filter (fun B : Finset X => A ⊆ B) = Finset.Ici A := by
    ext B
    simp
  rw [upperMobius, hs]
  apply Finset.sum_congr rfl
  intro B hB
  rw [← booleanMu_eq_mu]
  simp [booleanMu, Finset.mem_Ici.mp hB]
end EconomicsNextProof
end
end

set_option autoImplicit true
@[expose] public section
public section
open EconomicsNextProof
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace EconomicsNextProof
theorem _root_.solution (f : Finset X → ℝ) : upperMobius (upperSum f) = f := by
  funext A
  rw [upperMobius_eq_mu]
  exact (IncidenceAlgebra.moebius_inversion_top f (upperSum f)
    (fun B => upperSum_eq_Ici f B) A).symm
end EconomicsNextProof
