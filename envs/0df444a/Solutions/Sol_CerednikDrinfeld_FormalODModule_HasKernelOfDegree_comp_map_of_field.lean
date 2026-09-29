-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dd9a20ed-d260-5598-a3df-548f55aaaf38

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

noncomputable section

open MvPowerSeries

namespace R4CompField

section Vars

variable {d : ℕ} {R : Type u} [CommRing R]

abbrev mX (d : ℕ) (R : Type u) [CommRing R] : Ideal (MvPowerSeries (Fin d) R) :=
  Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) R))

def lowIdeal (d : ℕ) (R : Type u) [CommRing R] (N : ℕ) : Ideal (MvPowerSeries (Fin d) R) where
  carrier := {q | ∀ x : Fin d →₀ ℕ, x.degree < N → coeff x q = 0}
  add_mem' {a b} ha hb x hx := by rw [map_add, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by rw [map_zero]
  smul_mem' a q hq x hx := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.sum_eq_zero fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : ij.2 ≤ x := hij ▸ le_add_self
    rw [hq ij.2 ((Finsupp.degree_mono hj).trans_lt hx), mul_zero]

theorem span_X_le_lowIdeal_one : mX d R ≤ lowIdeal d R 1 := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩ x hx
  have hx0 : x = 0 := (Finsupp.degree_eq_zero_iff x).mp (Nat.lt_one_iff.mp hx)
  subst hx0
  exact coeff_zero_X i

theorem lowIdeal_mul_le (a b : ℕ) : lowIdeal d R a * lowIdeal d R b ≤ lowIdeal d R (a + b) := by
  classical
  rw [Ideal.mul_le]
  intro r hr s hs x hx
  show coeff x (r * s) = 0
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : ij.1.degree < a
  · rw [hr ij.1 hi, zero_mul]
  · have hdeg : x.degree = ij.1.degree + ij.2.degree := by rw [← hij, map_add]
    have hj : ij.2.degree < b := by omega
    rw [hs ij.2 hj, mul_zero]

theorem pow_mX_le_lowIdeal (N : ℕ) : mX d R ^ N ≤ lowIdeal d R N := by
  induction N with
  | zero =>
    intro q _ x hx
    exact absurd hx (Nat.not_lt_zero _)
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih span_X_le_lowIdeal_one).trans (lowIdeal_mul_le n 1)

theorem coeff_eq_zero_of_mem_pow {N : ℕ} {q : MvPowerSeries (Fin d) R} (hq : q ∈ mX d R ^ N)
    (x : Fin d →₀ ℕ) (hx : x.degree < N) : coeff x q = 0 :=
  pow_mX_le_lowIdeal N hq x hx

theorem mem_pow_of_coeff_eq_zero {N : ℕ} {q : MvPowerSeries (Fin d) R}
    (hq : ∀ x : Fin d →₀ ℕ, x.degree < N → coeff x q = 0) : q ∈ mX d R ^ N :=
  MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero N q hq

theorem eq_zero_of_forall_mem_pow {q : MvPowerSeries (Fin d) R} (hq : ∀ N, q ∈ mX d R ^ N) :
    q = 0 := by
  ext x
  rw [map_zero]
  exact coeff_eq_zero_of_mem_pow (hq (x.degree + 1)) x (Nat.lt_succ_self _)

theorem pow_mul_le_of_pow_le {A : Type u} [CommRing A] {I J : Ideal A} {N : ℕ} (h : I ^ N ≤ J) (n : ℕ) :
    I ^ (N * n) ≤ J ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono h n

noncomputable def SFin (d N : ℕ) : Finset (Fin d →₀ ℕ) := (Finsupp.finite_of_degree_lt N).toFinset

theorem mem_SFin {N : ℕ} (x : Fin d →₀ ℕ) : x ∈ SFin d N ↔ x.degree < N := by
  rw [SFin, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

theorem coeff_sum_monomial (S : Finset (Fin d →₀ ℕ)) (a : (Fin d →₀ ℕ) → R) (x : Fin d →₀ ℕ) :
    coeff x (∑ m ∈ S, monomial m (a m)) = if x ∈ S then a x else 0 := by
  classical
  rw [map_sum]
  simp_rw [coeff_monomial]
  rw [Finset.sum_ite_eq]

noncomputable def lowPart (N : ℕ) (q : MvPowerSeries (Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ m ∈ SFin d N, monomial m (coeff m q)

theorem coeff_lowPart (N : ℕ) (q : MvPowerSeries (Fin d) R) (x : Fin d →₀ ℕ) :
    coeff x (lowPart N q) = if x.degree < N then coeff x q else 0 := by
  rw [lowPart, coeff_sum_monomial]
  simp only [mem_SFin]

theorem sub_lowPart_mem_pow (N : ℕ) (q : MvPowerSeries (Fin d) R) :
    q - lowPart N q ∈ mX d R ^ N := by
  refine mem_pow_of_coeff_eq_zero fun x hx => ?_
  rw [map_sub, coeff_lowPart, if_pos hx, sub_self]

theorem monomial_eq_smul (m : Fin d →₀ ℕ) (r : R) :
    (monomial m r : MvPowerSeries (Fin d) R) = r • monomial m 1 := by
  rw [← map_smul, smul_eq_mul, mul_one]

theorem lowPart_eq_sum_smul (N : ℕ) (q : MvPowerSeries (Fin d) R) :
    lowPart N q = ∑ m ∈ SFin d N, coeff m q • monomial m (1 : R) := by
  refine Finset.sum_congr rfl fun m _ => monomial_eq_smul m _

theorem lowPart_eq_zero_of_forall {N : ℕ} {q : MvPowerSeries (Fin d) R}
    (h : ∀ x : Fin d →₀ ℕ, x.degree < N → coeff x q = 0) : lowPart N q = 0 := by
  ext x
  rw [coeff_lowPart, map_zero]
  split_ifs with hx
  · exact h x hx
  · rfl

variable {R' : Type u} [CommRing R']

theorem map_monomial_one (f : R →+* R') (m : Fin d →₀ ℕ) :
    map f (monomial m (1 : R)) = monomial m 1 := by
  rw [map_monomial, map_one]

theorem map_mX (f : R →+* R') : (mX d R).map (MvPowerSeries.map (σ := Fin d) f) = mX d R' := by
  rw [Ideal.map_span, ← Set.range_comp]
  congr 1
  ext q
  simp only [Set.mem_range, Function.comp_apply, MvPowerSeries.map_X]

theorem map_span_range {ι : Type*} (f : R →+* R') (φ : ι → MvPowerSeries (Fin d) R) :
    (Ideal.span (Set.range φ)).map (MvPowerSeries.map (σ := Fin d) f) =
      Ideal.span (Set.range fun i => MvPowerSeries.map f (φ i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

end Vars

section Subst

variable {d : ℕ} {B : Type u} [CommRing B]
variable {χ : Fin d → MvPowerSeries (Fin d) B}

theorem hasSubst_of (hχ : ∀ i, constantCoeff (χ i) = 0) : HasSubst χ :=
  hasSubst_of_constantCoeff_zero hχ

noncomputable def theta (hχ : ∀ i, constantCoeff (χ i) = 0) :
    MvPowerSeries (Fin d) B →ₐ[B] MvPowerSeries (Fin d) B :=
  substAlgHom (hasSubst_of hχ)

theorem theta_apply (hχ : ∀ i, constantCoeff (χ i) = 0) (q : MvPowerSeries (Fin d) B) :
    theta hχ q = subst χ q :=
  substAlgHom_apply _ q

theorem subst_add' (hχ : ∀ i, constantCoeff (χ i) = 0) (q q' : MvPowerSeries (Fin d) B) :
    subst χ (q + q') = subst χ q + subst χ q' := by
  rw [← theta_apply hχ, ← theta_apply hχ, ← theta_apply hχ, map_add]

theorem subst_mul' (hχ : ∀ i, constantCoeff (χ i) = 0) (q q' : MvPowerSeries (Fin d) B) :
    subst χ (q * q') = subst χ q * subst χ q' := by
  rw [← theta_apply hχ, ← theta_apply hχ, ← theta_apply hχ, map_mul]

theorem subst_sub' (hχ : ∀ i, constantCoeff (χ i) = 0) (q q' : MvPowerSeries (Fin d) B) :
    subst χ (q - q') = subst χ q - subst χ q' := by
  rw [← theta_apply hχ, ← theta_apply hχ, ← theta_apply hχ, map_sub]

theorem subst_zero' (hχ : ∀ i, constantCoeff (χ i) = 0) :
    subst χ (0 : MvPowerSeries (Fin d) B) = 0 := by
  rw [← theta_apply hχ, map_zero]

theorem subst_smul' (hχ : ∀ i, constantCoeff (χ i) = 0) (r : B) (q : MvPowerSeries (Fin d) B) :
    subst χ (r • q) = r • subst χ q := by
  rw [← theta_apply hχ, ← theta_apply hχ, map_smul]

theorem subst_sum' (hχ : ∀ i, constantCoeff (χ i) = 0) {ι : Type*} (s : Finset ι)
    (q : ι → MvPowerSeries (Fin d) B) : subst χ (∑ i ∈ s, q i) = ∑ i ∈ s, subst χ (q i) := by
  simp_rw [← theta_apply hχ]
  rw [map_sum]

theorem map_theta_mX (hχ : ∀ i, constantCoeff (χ i) = 0) :
    (mX d B).map (theta hχ) = Ideal.span (Set.range χ) := by
  rw [Ideal.map_span]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by rw [theta_apply, subst_X (hasSubst_of hχ)]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨X i, ⟨i, rfl⟩, by rw [theta_apply, subst_X (hasSubst_of hχ)]⟩

theorem subst_mem_pow_of_mem_pow (hχ : ∀ i, constantCoeff (χ i) = 0) {n : ℕ}
    {q : MvPowerSeries (Fin d) B} (hq : q ∈ mX d B ^ n) : subst χ q ∈ Ideal.span (Set.range χ) ^ n := by
  rw [← map_theta_mX hχ, ← Ideal.map_pow, ← theta_apply hχ]
  exact Ideal.mem_map_of_mem _ hq

theorem span_le_mX (hχ : ∀ i, constantCoeff (χ i) = 0) : Ideal.span (Set.range χ) ≤ mX d B := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  show χ i ∈ mX d B
  rw [mX, MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker]
  exact hχ i

theorem constantCoeff_map_eq_zero (hχ : ∀ i, constantCoeff (χ i) = 0) {B' : Type u} [CommRing B']
    (f : B →+* B') (i : Fin d) : constantCoeff (MvPowerSeries.map f (χ i)) = 0 := by
  rw [constantCoeff_map, hχ i, map_zero]

def Theta {b : ℕ} (χ : Fin d → MvPowerSeries (Fin d) B) (ε : Fin b → MvPowerSeries (Fin d) B)
    (c : Fin b → MvPowerSeries (Fin d) B) : MvPowerSeries (Fin d) B :=
  ∑ i, subst χ (c i) * ε i

variable {b : ℕ} {ε : Fin b → MvPowerSeries (Fin d) B}

theorem Theta_add (hχ : ∀ i, constantCoeff (χ i) = 0) (c c' : Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (c + c') = Theta χ ε c + Theta χ ε c' := by
  rw [Theta, Theta, Theta, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, subst_add' hχ, add_mul]

theorem Theta_zero (hχ : ∀ i, constantCoeff (χ i) = 0) : Theta χ ε 0 = 0 := by
  rw [Theta]
  exact Finset.sum_eq_zero fun i _ => by rw [Pi.zero_apply, subst_zero' hχ, zero_mul]

theorem Theta_sub (hχ : ∀ i, constantCoeff (χ i) = 0) (c c' : Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (c - c') = Theta χ ε c - Theta χ ε c' := by
  rw [Theta, Theta, Theta, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply, subst_sub' hχ, sub_mul]

theorem Theta_mul_left (hχ : ∀ i, constantCoeff (χ i) = 0) (a : MvPowerSeries (Fin d) B)
    (c : Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (fun i => a * c i) = subst χ a * Theta χ ε c := by
  rw [Theta, Theta, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [subst_mul' hχ, mul_assoc]

theorem Theta_smul (hχ : ∀ i, constantCoeff (χ i) = 0) (r : B) (c : Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (r • c) = r • Theta χ ε c := by
  rw [Theta, Theta, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, subst_smul' hχ, smul_mul_assoc]

theorem Theta_finset_sum (hχ : ∀ i, constantCoeff (χ i) = 0) {ι : Type*} (s : Finset ι)
    (c : ι → Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (∑ k ∈ s, c k) = ∑ k ∈ s, Theta χ ε (c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Theta_zero hχ]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Theta_add hχ, ih]

theorem mul_Theta_eq (hχ : ∀ i, constantCoeff (χ i) = 0) (a : MvPowerSeries (Fin d) B)
    (v : Fin b → Fin b → MvPowerSeries (Fin d) B) (hv : ∀ i, a * ε i = Theta χ ε (v i))
    (c : Fin b → MvPowerSeries (Fin d) B) :
    a * Theta χ ε c = Theta χ ε (fun k => ∑ i, c i * v i k) := by
  calc a * Theta χ ε c = ∑ i, subst χ (c i) * (a * ε i) := by
          rw [Theta, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, subst χ (c i) * Theta χ ε (v i) := Finset.sum_congr rfl fun i _ => by rw [hv i]
    _ = ∑ i, Theta χ ε (fun k => c i * v i k) :=
          Finset.sum_congr rfl fun i _ => by rw [Theta_mul_left hχ]
    _ = Theta χ ε (∑ i, fun k => c i * v i k) := (Theta_finset_sum hχ _ _).symm
    _ = Theta χ ε (fun k => ∑ i, c i * v i k) := by
          congr 1
          funext k
          rw [Finset.sum_apply]

theorem Theta_mem_pow (hχ : ∀ i, constantCoeff (χ i) = 0) {n : ℕ} {c : Fin b → MvPowerSeries (Fin d) B}
    (hc : ∀ i, c i ∈ mX d B ^ n) : Theta χ ε c ∈ Ideal.span (Set.range χ) ^ n := by
  rw [Theta]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (subst_mem_pow_of_mem_pow hχ (hc i))

theorem exists_coords_of_mem_map (hχ : ∀ i, constantCoeff (χ i) = 0)
    (hspan : ∀ x, ∃ c, x = Theta χ ε c) (J : Ideal (MvPowerSeries (Fin d) B))
    {y : MvPowerSeries (Fin d) B} (hy : y ∈ J.map (theta hχ)) :
    ∃ c : Fin b → MvPowerSeries (Fin d) B, (∀ i, c i ∈ J) ∧ Theta χ ε c = y := by
  rw [Ideal.map] at hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨u, hu⟩ := hspan 1
    refine ⟨fun i => j * u i, fun i => J.mul_mem_right _ hj, ?_⟩
    rw [Theta_mul_left hχ, ← hu, mul_one, theta_apply]
  · exact ⟨0, fun _ => J.zero_mem, Theta_zero hχ⟩
  · rintro x y - - ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨c + c', fun i => J.add_mem (hc i) (hc' i), Theta_add hχ c c'⟩
  · rintro a y - ⟨c, hc, rfl⟩
    choose v hv using fun i => hspan (a * ε i)
    refine ⟨fun k => ∑ i, c i * v i k, fun k => J.sum_mem fun i _ => J.mul_mem_right _ (hc i), ?_⟩
    rw [smul_eq_mul, mul_Theta_eq hχ a v hv c]

theorem mem_pow_of_Theta_mem_pow (hχ : ∀ i, constantCoeff (χ i) = 0)
    (hspan : ∀ x, ∃ c, x = Theta χ ε c) (hinj : ∀ c c', Theta χ ε c = Theta χ ε c' → c = c')
    {n : ℕ} {c : Fin b → MvPowerSeries (Fin d) B} (hc : Theta χ ε c ∈ Ideal.span (Set.range χ) ^ n)
    (i : Fin b) : c i ∈ mX d B ^ n := by
  rw [← map_theta_mX hχ, ← Ideal.map_pow] at hc
  obtain ⟨c', hc', heq⟩ := exists_coords_of_mem_map hχ hspan _ hc
  rw [hinj c c' heq.symm]
  exact hc' i

variable {B' : Type u} [CommRing B']

theorem map_subst' (hχ : ∀ i, constantCoeff (χ i) = 0) (f : B →+* B') (q : MvPowerSeries (Fin d) B) :
    MvPowerSeries.map f (subst χ q) = subst (fun i => MvPowerSeries.map f (χ i)) (MvPowerSeries.map f q) :=
  map_subst (hasSubst_of hχ) q

theorem map_Theta (hχ : ∀ i, constantCoeff (χ i) = 0) (f : B →+* B') (c : Fin b → MvPowerSeries (Fin d) B) :
    MvPowerSeries.map f (Theta χ ε c) =
      Theta (fun i => MvPowerSeries.map f (χ i)) (fun i => MvPowerSeries.map f (ε i))
        (fun i => MvPowerSeries.map f (c i)) := by
  rw [Theta, Theta, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_subst' hχ]

end Subst

structure Coord (d b : ℕ) (B : Type u) [CommRing B] where

  χ : Fin d → MvPowerSeries (Fin d) B
  hχ : ∀ i, constantCoeff (χ i) = 0

  ε : Fin b → MvPowerSeries (Fin d) B
  span : ∀ x, ∃ c, x = Theta χ ε c
  inj : ∀ c c', Theta χ ε c = Theta χ ε c' → c = c'

section CoordBasic

variable {d b : ℕ} {B : Type u} [CommRing B]
variable {χ : Fin d → MvPowerSeries (Fin d) B} {ε : Fin b → MvPowerSeries (Fin d) B}

def wv (χ : Fin d → MvPowerSeries (Fin d) B) (ε : Fin b → MvPowerSeries (Fin d) B) (n : ℕ)
    (im : Fin b × ↥(SFin d n)) : MvPowerSeries (Fin d) B :=
  subst χ (monomial (im.2 : Fin d →₀ ℕ) (1 : B)) * ε im.1

theorem Theta_lowc (hχ : ∀ i, constantCoeff (χ i) = 0) (n : ℕ) (g : Fin b × ↥(SFin d n) → B) :
    Theta χ ε (fun i => ∑ m : ↥(SFin d n), monomial (m : Fin d →₀ ℕ) (g (i, m))) =
      ∑ im : Fin b × ↥(SFin d n), g im • wv χ ε n im := by
  rw [Fintype.sum_prod_type, Theta]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [subst_sum' hχ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [wv, monomial_eq_smul, subst_smul' hχ, smul_mul_assoc]

theorem coeff_sum_subtype (n : ℕ) (g : ↥(SFin d n) → B) (x : Fin d →₀ ℕ) (hx : x ∈ SFin d n) :
    coeff x (∑ m : ↥(SFin d n), monomial (m : Fin d →₀ ℕ) (g m)) = g ⟨x, hx⟩ := by
  classical
  rw [map_sum, Finset.sum_eq_single (⟨x, hx⟩ : ↥(SFin d n))]
  · rw [coeff_monomial, if_pos rfl]
  · rintro m - hm
    rw [coeff_monomial, if_neg]
    intro h
    exact hm (Subtype.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem lowPart_eq_sum_subtype (n : ℕ) (q : MvPowerSeries (Fin d) B) :
    lowPart n q = ∑ m : ↥(SFin d n), monomial (m : Fin d →₀ ℕ) (coeff (m : Fin d →₀ ℕ) q) := by
  rw [lowPart, ← Finset.sum_coe_sort]

theorem Theta_lowPart (hχ : ∀ i, constantCoeff (χ i) = 0) (n : ℕ) (c : Fin b → MvPowerSeries (Fin d) B) :
    Theta χ ε (fun i => lowPart n (c i)) =
      ∑ im : Fin b × ↥(SFin d n), coeff (im.2 : Fin d →₀ ℕ) (c im.1) • wv χ ε n im := by
  rw [← Theta_lowc hχ n fun im => coeff (im.2 : Fin d →₀ ℕ) (c im.1)]
  congr 1
  funext i
  exact lowPart_eq_sum_subtype n (c i)

variable {B' : Type u} [CommRing B']

theorem wv_map (hχ : ∀ i, constantCoeff (χ i) = 0) (f : B →+* B') (n : ℕ) (im : Fin b × ↥(SFin d n)) :
    wv (fun i => MvPowerSeries.map f (χ i)) (fun i => MvPowerSeries.map f (ε i)) n im =
      MvPowerSeries.map f (wv χ ε n im) := by
  rw [wv, wv, map_mul, map_subst' hχ, map_monomial_one]

variable (K : Coord d b B)

theorem Coord.mem_pow (n : ℕ) {c : Fin b → MvPowerSeries (Fin d) B}
    (hc : Theta K.χ K.ε c ∈ Ideal.span (Set.range K.χ) ^ n) (i : Fin b) : c i ∈ mX d B ^ n :=
  mem_pow_of_Theta_mem_pow K.hχ K.span K.inj hc i

end CoordBasic

section Field

variable {d : ℕ} {κ : Type u} [Field κ]

theorem exists_pow_mX_le_of_finite (I : Ideal (MvPowerSeries (Fin d) κ))
    [Module.Finite κ (MvPowerSeries (Fin d) κ ⧸ I)] : ∃ N : ℕ, mX d κ ^ N ≤ I := by
  haveI : IsArtinianRing (MvPowerSeries (Fin d) κ ⧸ I) :=
    IsArtinianRing.of_finite κ (MvPowerSeries (Fin d) κ ⧸ I)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MvPowerSeries (Fin d) κ ⧸ I)
  refine ⟨N, ?_⟩
  have hle : (mX d κ).map (Ideal.Quotient.mk I) ≤ Ideal.jacobson ⊥ := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_jacobson_bot]
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), ← map_add]
    refine IsUnit.map _ ?_
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, map_mul, constantCoeff_X, zero_mul,
      zero_add, map_one]
    exact isUnit_one
  have h2 : ((mX d κ).map (Ideal.Quotient.mk I)) ^ N = ⊥ := by
    rw [eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_right_mono hle N
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at h2
  exact h2

theorem span_ne_top {χ : Fin d → MvPowerSeries (Fin d) κ} (hχ : ∀ i, constantCoeff (χ i) = 0) :
    Ideal.span (Set.range χ) ≠ ⊤ := by
  intro h
  have h1 : (1 : MvPowerSeries (Fin d) κ) ∈ mX d κ := span_le_mX hχ (h ▸ Submodule.mem_top)
  rw [mX, MvPowerSeries.span_range_X_eq_ker_constantCoeff, RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

theorem finrank_pos_of {χ : Fin d → MvPowerSeries (Fin d) κ} (hχ : ∀ i, constantCoeff (χ i) = 0)
    [Module.Finite κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range χ))] :
    0 < Module.finrank κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range χ)) := by
  haveI : Nontrivial (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range χ)) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_ne_top hχ)
  exact Module.finrank_pos

theorem exists_coord (φ : Fin d → MvPowerSeries (Fin d) κ) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range φ))) :
    ∃ K : Coord d (Module.finrank κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range φ))) κ,
      K.χ = φ := by
  obtain ⟨-, -, e, he⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient φ hφ hfin
  refine ⟨⟨φ, hφ, e, fun x => ?_, fun c c' h => ?_⟩, rfl⟩
  · obtain ⟨c, hc, -⟩ := he x
    exact ⟨c, hc⟩
  · obtain ⟨c₀, -, huniq⟩ := he (Theta φ e c)
    exact (huniq c rfl).trans (huniq c' h).symm

variable {b : ℕ} (K : Coord d b κ)

abbrev Coord.V (n : ℕ) : Type u := MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range K.χ) ^ n

def Coord.mkV (n : ℕ) : MvPowerSeries (Fin d) κ →ₗ[κ] K.V n :=
  (Ideal.Quotient.mkₐ κ (Ideal.span (Set.range K.χ) ^ n)).toLinearMap

theorem Coord.mkV_apply (n : ℕ) (x : MvPowerSeries (Fin d) κ) :
    K.mkV n x = Ideal.Quotient.mk (Ideal.span (Set.range K.χ) ^ n) x := rfl

theorem Coord.mkV_eq_zero (n : ℕ) {x : MvPowerSeries (Fin d) κ}
    (hx : x ∈ Ideal.span (Set.range K.χ) ^ n) : K.mkV n x = 0 := by
  rw [Coord.mkV_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact hx

theorem Coord.linearIndependent (n : ℕ) :
    LinearIndependent κ (fun im : Fin b × ↥(SFin d n) => K.mkV n (wv K.χ K.ε n im)) := by
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨i, m⟩
  have h1 : K.mkV n (Theta K.χ K.ε
      (fun i => ∑ m : ↥(SFin d n), monomial (m : Fin d →₀ ℕ) (g (i, m)))) = 0 := by
    rw [Theta_lowc K.hχ n g, map_sum]
    simpa only [map_smul] using hg
  rw [Coord.mkV_apply, Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 := K.mem_pow n h1 i
  have h3 := coeff_eq_zero_of_mem_pow h2 (m : Fin d →₀ ℕ) ((mem_SFin _).mp m.2)
  rw [coeff_sum_subtype n (fun m' => g (i, m')) _ m.2] at h3
  exact h3

theorem Coord.span_top (n : ℕ) :
    ⊤ ≤ Submodule.span κ (Set.range fun im : Fin b × ↥(SFin d n) => K.mkV n (wv K.χ K.ε n im)) := by
  rintro v -
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective v
  obtain ⟨c, rfl⟩ := K.span x
  have hsplit : c = (fun i => lowPart n (c i)) + (c - fun i => lowPart n (c i)) := by
    rw [add_sub_cancel]
  have hhigh : K.mkV n (Theta K.χ K.ε (c - fun i => lowPart n (c i))) = 0 :=
    K.mkV_eq_zero n (Theta_mem_pow K.hχ (c := c - fun i => lowPart n (c i))
      fun i => sub_lowPart_mem_pow n (c i))
  rw [← Coord.mkV_apply, hsplit, Theta_add K.hχ, map_add, Theta_lowPart K.hχ n c, map_sum, hhigh,
    add_zero]
  refine Submodule.sum_mem _ fun im _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨im, rfl⟩)

def Coord.bV (n : ℕ) : Module.Basis (Fin b × ↥(SFin d n)) κ (K.V n) :=
  Module.Basis.mk (K.linearIndependent n) (K.span_top n)

theorem Coord.bV_apply (n : ℕ) (im : Fin b × ↥(SFin d n)) : K.bV n im = K.mkV n (wv K.χ K.ε n im) :=
  Module.Basis.mk_apply _ _ im

def Coord.ell (n : ℕ) (im : Fin b × ↥(SFin d n)) : MvPowerSeries (Fin d) κ →ₗ[κ] κ :=
  ((K.bV n).coord im).comp (K.mkV n)

theorem Coord.ell_wv (n : ℕ) (im im' : Fin b × ↥(SFin d n)) :
    K.ell n im (wv K.χ K.ε n im') = if im' = im then 1 else 0 := by
  classical
  rw [Coord.ell, LinearMap.comp_apply, ← K.bV_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]

theorem Coord.ell_eq_zero (n : ℕ) (im : Fin b × ↥(SFin d n)) {y : MvPowerSeries (Fin d) κ}
    (hy : y ∈ Ideal.span (Set.range K.χ) ^ n) : K.ell n im y = 0 := by
  rw [Coord.ell, LinearMap.comp_apply, K.mkV_eq_zero n hy, map_zero]

end Field

section BaseChange

variable {d b : ℕ} {κ : Type u} [Field κ] (K : Coord d b κ) {R : Type u} [CommRing R] (f : κ →+* R)

def Coord.χR : Fin d → MvPowerSeries (Fin d) R := fun i => MvPowerSeries.map f (K.χ i)

def Coord.εR : Fin b → MvPowerSeries (Fin d) R := fun i => MvPowerSeries.map f (K.ε i)

theorem Coord.hχR : ∀ i, constantCoeff (K.χR f i) = 0 := fun i => constantCoeff_map_eq_zero K.hχ f i

theorem Coord.ThetaR_map (c : Fin b → MvPowerSeries (Fin d) κ) :
    Theta (K.χR f) (K.εR f) (fun i => MvPowerSeries.map f (c i)) =
      MvPowerSeries.map f (Theta K.χ K.ε c) :=
  (map_Theta K.hχ f c).symm

theorem Coord.wvR_eq (n : ℕ) (im : Fin b × ↥(SFin d n)) :
    wv (K.χR f) (K.εR f) n im = MvPowerSeries.map f (wv K.χ K.ε n im) :=
  wv_map K.hχ f n im

theorem Coord.pow_le_spanR {N : ℕ} (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ)) :
    mX d R ^ N ≤ Ideal.span (Set.range (K.χR f)) := by
  have := Ideal.map_mono (f := MvPowerSeries.map (σ := Fin d) f) hN
  rwa [Ideal.map_pow, map_mX, map_span_range] at this

theorem Coord.exists_sub_ThetaR_mem_pow {N : ℕ} (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ))
    (n : ℕ) (x : MvPowerSeries (Fin d) R) :
    ∃ c, x - Theta (K.χR f) (K.εR f) c ∈ Ideal.span (Set.range (K.χR f)) ^ n := by
  classical
  choose cm hcm using fun m : Fin d →₀ ℕ => K.span (monomial m (1 : κ))
  refine ⟨∑ m ∈ SFin d (N * n), coeff m x • fun i => MvPowerSeries.map f (cm m i), ?_⟩
  have hlow : lowPart (N * n) x = Theta (K.χR f) (K.εR f)
      (∑ m ∈ SFin d (N * n), coeff m x • fun i => MvPowerSeries.map f (cm m i)) := by
    rw [lowPart_eq_sum_smul, Theta_finset_sum (K.hχR f)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Theta_smul (K.hχR f), K.ThetaR_map f, ← hcm m, map_monomial_one]
  rw [← hlow]
  exact pow_mul_le_of_pow_le (K.pow_le_spanR f hN) n (sub_lowPart_mem_pow _ x)

def Coord.Lam (N n : ℕ) (im : Fin b × ↥(SFin d n)) : MvPowerSeries (Fin d) R →ₗ[R] R :=
  ∑ μ ∈ SFin d (N * n), f (K.ell n im (monomial μ 1)) •
    (MvPowerSeries.coeff μ : MvPowerSeries (Fin d) R →ₗ[R] R)

theorem Coord.Lam_apply (N n : ℕ) (im : Fin b × ↥(SFin d n)) (y : MvPowerSeries (Fin d) R) :
    K.Lam f N n im y = ∑ μ ∈ SFin d (N * n), f (K.ell n im (monomial μ 1)) * coeff μ y := by
  rw [Coord.Lam, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul]

theorem Coord.Lam_eq_zero_of_mem_pow (N n : ℕ) (im : Fin b × ↥(SFin d n))
    {y : MvPowerSeries (Fin d) R} (hy : y ∈ mX d R ^ (N * n)) : K.Lam f N n im y = 0 := by
  rw [Coord.Lam_apply]
  exact Finset.sum_eq_zero fun μ hμ => by
    rw [coeff_eq_zero_of_mem_pow hy μ ((mem_SFin μ).mp hμ), mul_zero]

theorem Coord.Lam_map (N n : ℕ) (im : Fin b × ↥(SFin d n))
    (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ)) (z : MvPowerSeries (Fin d) κ) :
    K.Lam f N n im (MvPowerSeries.map f z) = f (K.ell n im z) := by
  have hz : K.ell n im z = K.ell n im (lowPart (N * n) z) := by
    have h := K.ell_eq_zero n im (pow_mul_le_of_pow_le hN n (sub_lowPart_mem_pow (N * n) z))
    rw [map_sub, sub_eq_zero] at h
    exact h
  rw [hz, lowPart_eq_sum_smul, map_sum, map_sum, Coord.Lam_apply]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, smul_eq_mul, map_mul, coeff_map, mul_comm]

theorem Coord.Lam_eq_zero_of_mem_spanR_pow (N n : ℕ) (im : Fin b × ↥(SFin d n))
    (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ)) {y : MvPowerSeries (Fin d) R}
    (hy : y ∈ Ideal.span (Set.range (K.χR f)) ^ n) : K.Lam f N n im y = 0 := by
  have hJ : Ideal.span (Set.range (K.χR f)) ^ n =
      ((Ideal.span (Set.range K.χ)) ^ n).map (MvPowerSeries.map f) := by
    rw [Ideal.map_pow, map_span_range]
    rfl
  rw [hJ, Ideal.map] at hy
  suffices h : ∀ a, K.Lam f N n im (a * y) = 0 by simpa only [one_mul] using h 1
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨j, hj, rfl⟩ a
    have ha : a = lowPart (N * n) a + (a - lowPart (N * n) a) := (add_sub_cancel _ _).symm
    rw [ha, add_mul, map_add, K.Lam_eq_zero_of_mem_pow f N n im
      (Ideal.mul_mem_right _ _ (sub_lowPart_mem_pow _ a)), add_zero, lowPart_eq_sum_smul,
      Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [smul_mul_assoc, map_smul, ← map_monomial_one f μ, ← map_mul, K.Lam_map f N n im hN,
      K.ell_eq_zero n im (Ideal.mul_mem_left _ _ hj), map_zero, smul_zero]
  · intro a
    rw [mul_zero, map_zero]
  · intro x y _ _ hx hy a
    rw [mul_add, map_add, hx a, hy a, add_zero]
  · intro r x _ hx a
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (a * r)

theorem Coord.mem_pow_of_ThetaR_mem_pow {N : ℕ} (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ))
    (n : ℕ) {c : Fin b → MvPowerSeries (Fin d) R}
    (hc : Theta (K.χR f) (K.εR f) c ∈ Ideal.span (Set.range (K.χR f)) ^ n) (i : Fin b) :
    c i ∈ mX d R ^ n := by
  classical
  have hhi : ∀ i, (c - fun i => lowPart n (c i)) i ∈ mX d R ^ n := fun i => sub_lowPart_mem_pow n (c i)
  have hloc : Theta (K.χR f) (K.εR f) (fun i => lowPart n (c i)) ∈
      Ideal.span (Set.range (K.χR f)) ^ n := by
    have h := Ideal.sub_mem _ hc
      (Theta_mem_pow (K.hχR f) (ε := K.εR f) (c := c - fun i => lowPart n (c i)) hhi)
    rwa [← Theta_sub (K.hχR f), sub_sub_cancel] at h
  have hcoef : ∀ im : Fin b × ↥(SFin d n), coeff (im.2 : Fin d →₀ ℕ) (c im.1) = 0 := by
    intro im₀
    have h0 := K.Lam_eq_zero_of_mem_spanR_pow f N n im₀ hN hloc
    rw [Theta_lowPart (K.hχR f) n c, map_sum, Finset.sum_eq_single im₀] at h0
    · rw [map_smul, K.wvR_eq f, K.Lam_map f N n im₀ hN, K.ell_wv, if_pos rfl, map_one, smul_eq_mul,
        mul_one] at h0
      exact h0
    · intro im _ him
      rw [map_smul, K.wvR_eq f, K.Lam_map f N n im₀ hN, K.ell_wv, if_neg him, map_zero, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hlo : lowPart n (c i) = 0 :=
    lowPart_eq_zero_of_forall fun x hx => hcoef (i, ⟨x, (mem_SFin x).mpr hx⟩)
  have := hhi i
  rwa [Pi.sub_apply, hlo, sub_zero] at this

theorem Coord.ThetaR_injective {N : ℕ} (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ))
    (c c' : Fin b → MvPowerSeries (Fin d) R)
    (h : Theta (K.χR f) (K.εR f) c = Theta (K.χR f) (K.εR f) c') : c = c' := by
  rw [← sub_eq_zero]
  funext i
  refine eq_zero_of_forall_mem_pow fun n => ?_
  refine K.mem_pow_of_ThetaR_mem_pow f hN n ?_ i
  rw [Theta_sub (K.hχR f), h, sub_self]
  exact Ideal.zero_mem _

theorem Coord.ThetaR_surjective {N : ℕ} (hN : mX d κ ^ N ≤ Ideal.span (Set.range K.χ))
    (x : MvPowerSeries (Fin d) R) : ∃ c, x = Theta (K.χR f) (K.εR f) c := by
  choose c hc using fun n => K.exists_sub_ThetaR_mem_pow f hN n x
  have hcompat : ∀ k n, k ≤ n → ∀ i, (c n - c k) i ∈ mX d R ^ k := by
    intro k n hkn i
    refine K.mem_pow_of_ThetaR_mem_pow f hN k ?_ i
    have : Theta (K.χR f) (K.εR f) (c n - c k) =
        (x - Theta (K.χR f) (K.εR f) (c k)) - (x - Theta (K.χR f) (K.εR f) (c n)) := by
      rw [Theta_sub (K.hχR f)]
      ring
    rw [this]
    exact Ideal.sub_mem _ (hc k) (Ideal.pow_le_pow_right hkn (hc n))
  let clim : Fin b → MvPowerSeries (Fin d) R := fun i m => coeff m (c (m.degree + 1) i)
  have hclim : ∀ n i, clim i - c n i ∈ mX d R ^ n := by
    intro n i
    refine mem_pow_of_coeff_eq_zero fun m hm => ?_
    have h1 : coeff m (clim i) = coeff m (c (m.degree + 1) i) := rfl
    have h2 := coeff_eq_zero_of_mem_pow (hcompat (m.degree + 1) n hm i) m (Nat.lt_succ_self _)
    rw [Pi.sub_apply, map_sub] at h2
    rw [map_sub, h1, ← neg_sub, h2, neg_zero]
  refine ⟨clim, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_pow fun n => ?_
  have h1 : x - Theta (K.χR f) (K.εR f) clim =
      (x - Theta (K.χR f) (K.εR f) (c n)) - Theta (K.χR f) (K.εR f) (clim - c n) := by
    rw [Theta_sub (K.hχR f)]
    ring
  rw [h1]
  exact Ideal.pow_right_mono (span_le_mX (K.hχR f)) n
    (Ideal.sub_mem _ (hc n) (Theta_mem_pow (K.hχR f) (hclim n)))

def Coord.baseChange (hfin : Module.Finite κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range K.χ))) :
    Coord d b R where
  χ := K.χR f
  hχ := K.hχR f
  ε := K.εR f
  span x := by
    obtain ⟨N, hN⟩ := exists_pow_mX_le_of_finite (Ideal.span (Set.range K.χ))
    exact K.ThetaR_surjective f hN x
  inj c c' h := by
    obtain ⟨N, hN⟩ := exists_pow_mX_le_of_finite (Ideal.span (Set.range K.χ))
    exact K.ThetaR_injective f hN c c' h

@[scoped simp] theorem Coord.baseChange_χ (hfin : Module.Finite κ (MvPowerSeries (Fin d) κ ⧸ Ideal.span (Set.range K.χ))) :
    (K.baseChange f hfin).χ = fun i => MvPowerSeries.map f (K.χ i) := rfl

p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord"
end BaseChange
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord"

section Iso

variable {d b : ℕ} {B : Type u} [CommRing B] (K : Coord d b B) {ι' : Type*}
  (ψ : ι' → MvPowerSeries (Fin d) B)

theorem Coord.map_theta_span :
    (Ideal.span (Set.range ψ)).map (theta K.hχ) = Ideal.span (Set.range fun j => subst K.χ (ψ j)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, theta_apply]

def Coord.ThetaLin : (Fin b → MvPowerSeries (Fin d) B) →ₗ[B] MvPowerSeries (Fin d) B where
  toFun := Theta K.χ K.ε
  map_add' := Theta_add K.hχ
  map_smul' r c := Theta_smul K.hχ r c

def Coord.gam : (Fin b → MvPowerSeries (Fin d) B) →ₗ[B]
    MvPowerSeries (Fin d) B ⧸ Ideal.span (Set.range fun j => subst K.χ (ψ j)) :=
  (Ideal.Quotient.mkₐ B (Ideal.span (Set.range fun j => subst K.χ (ψ j)))).toLinearMap.comp K.ThetaLin

theorem Coord.gam_apply (c : Fin b → MvPowerSeries (Fin d) B) :
    K.gam ψ c = Ideal.Quotient.mk (Ideal.span (Set.range fun j => subst K.χ (ψ j))) (Theta K.χ K.ε c) :=
  rfl

theorem Coord.gam_surjective : Function.Surjective (K.gam ψ) := by
  intro v
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective v
  obtain ⟨c, rfl⟩ := K.span x
  exact ⟨c, rfl⟩

theorem Coord.ker_gam :
    LinearMap.ker (K.gam ψ) =
      Submodule.pi Set.univ (fun _ : Fin b => (Ideal.span (Set.range ψ)).restrictScalars B) := by
  ext c
  rw [LinearMap.mem_ker, Submodule.mem_pi, Coord.gam_apply, Ideal.Quotient.eq_zero_iff_mem,
    ← K.map_theta_span ψ]
  constructor
  · intro hc i _
    obtain ⟨c', hc', heq⟩ := exists_coords_of_mem_map K.hχ K.span _ hc
    rw [K.inj c c' heq.symm]
    exact hc' i
  · intro hc
    rw [Theta]
    refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_
    rw [← theta_apply K.hχ]
    exact Ideal.mem_map_of_mem _ (hc i (Set.mem_univ i))

def Coord.iso :
    (MvPowerSeries (Fin d) B ⧸ Ideal.span (Set.range fun j => subst K.χ (ψ j))) ≃ₗ[B]
      (Fin b → MvPowerSeries (Fin d) B ⧸ Ideal.span (Set.range ψ)) :=
  (LinearMap.quotKerEquivOfSurjective _ (K.gam_surjective ψ)).symm ≪≫ₗ
    (Submodule.quotEquivOfEq _ _ (K.ker_gam ψ)) ≪≫ₗ
    (Submodule.quotientPi fun _ : Fin b => (Ideal.span (Set.range ψ)).restrictScalars B) ≪≫ₗ
    (LinearEquiv.piCongrRight fun _ : Fin b =>
      Submodule.Quotient.restrictScalarsEquiv B (Ideal.span (Set.range ψ)))

theorem projective_pi {M : Type*} [AddCommGroup M] [Module B M] [Module.Projective B M] (n : ℕ) :
    Module.Projective B (Fin n → M) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := B) (M := fun _ : Fin n => M))

end Iso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord"

section Main

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem main {R : Type u} [CommRing R] {κ : Type u} [Field κ] (f : κ →+* R)
    {ψ : Series R} {a : ℕ} (hψ : FormalODModule.HasKernelOfDegree ψ a)
    {φ : Series κ} {b : ℕ} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ b) :
    FormalODModule.HasKernelOfDegree (ψ.comp (φ.map f)) (a * b) := by
  obtain ⟨hφfin, -, hφdeg⟩ := hφ
  obtain ⟨hψfin, hψproj, hψdeg⟩ := hψ
  obtain ⟨K, hK⟩ := exists_coord φ hφ0 hφfin
  have hbκ : Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ)) = b := by
    have := hφdeg κ (RingHom.id κ)
    rwa [Series.map_ringHom_id] at this
  have hbpos : 0 < Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ)) :=
    finrank_pos_of hφ0
  have hKfin : Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range K.χ)) := by
    rw [hK]; exact hφfin

  have key : ∀ (B' : Type u) [CommRing B'] (g' : κ →+* B') (ψ' : Series B'),
      Nonempty (FormalODModule.KerAlgebra (ψ'.comp (φ.map g')) ≃ₗ[B']
        (Fin (Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ))) →
          FormalODModule.KerAlgebra ψ')) := by
    intro B' _ g' ψ'
    have hχ : (K.baseChange g' hKfin).χ = φ.map g' := by
      rw [Coord.baseChange_χ, hK]
      rfl
    have e := (K.baseChange g' hKfin).iso ψ'
    rw [hχ] at e
    exact ⟨e⟩
  refine ⟨?_, ?_, fun κ' _ g => ?_⟩
  · obtain ⟨e⟩ := key R f ψ
    exact Module.Finite.equiv e.symm
  · obtain ⟨e⟩ := key R f ψ
    haveI := projective_pi (B := R) (M := FormalODModule.KerAlgebra ψ)
      (Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ)))
    exact Module.Projective.of_equiv e.symm
  · have hcomp : (ψ.comp (φ.map f)).map g = (ψ.map g).comp (φ.map (g.comp f)) := by
      rw [Series.map_comp g ψ (φ.map f) (fun i => constantCoeff_map_eq_zero hφ0 f i),
        Series.map_map]
    rw [hcomp]
    obtain ⟨e⟩ := key κ' (g.comp f) (ψ.map g)
    rw [LinearEquiv.finrank_eq e]
    by_cases hfin : Module.Finite κ' (FormalODModule.KerAlgebra (ψ.map g))
    · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        hψdeg κ' g, hbκ, smul_eq_mul, mul_comm]
    · have ha : a = 0 := by
        rw [← hψdeg κ' g]
        exact Module.finrank_of_not_finite hfin
      have hnf : ¬ Module.Finite κ'
          (Fin (Module.finrank κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ))) →
            FormalODModule.KerAlgebra (ψ.map g)) := by
        intro h
        exact hfin (Module.Finite.of_surjective
          (LinearMap.proj (R := κ') (φ := fun _ => FormalODModule.KerAlgebra (ψ.map g))
            (⟨0, hbpos⟩ : Fin _)) (LinearMap.proj_surjective _))
      rw [Module.finrank_of_not_finite hnf, ha, zero_mul]

end Main
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord"

end R4CompField
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField.Coord P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field.R4CompField"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {R : Type u} [CommRing R] {κ : Type u} [Field κ] (f : κ →+* R)
    {ψ : Series R} {a : ℕ} (hψ : FormalODModule.HasKernelOfDegree ψ a)
    {φ : Series κ} {b : ℕ} (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : FormalODModule.HasKernelOfDegree φ b) :
    FormalODModule.HasKernelOfDegree (ψ.comp (φ.map f)) (a * b) :=
  R4CompField.main f hψ hφ0 hφ

end S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field (solution)
