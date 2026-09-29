-- Prove2me | solution 1 for GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_forall_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/3ffaa559-dcdb-5d7d-93bf-b1a4e40d00b8

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_iff_span_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace CarayolMatrix

open IsLocalRing Matrix

section Generic

variable {S : Type*} [CommRing S] {m κ : Type*} [Fintype m] [DecidableEq m] [Fintype κ]
  [DecidableEq κ]

theorem gram_solve (M : κ → Matrix m m S) (Ginv : Matrix κ κ S)
    (hG : Ginv * Matrix.of (fun a b => Matrix.trace (M a * M b)) = 1) (c : κ → S)
    (X : Matrix m m S) (hX : X = ∑ a, c a • M a) :
    Ginv.mulVec (fun b => Matrix.trace (M b * X)) = c := by
  have h1 : (fun b => Matrix.trace (M b * X)) =
      (Matrix.of fun a b => Matrix.trace (M a * M b)).mulVec c := by
    funext b
    rw [hX, Finset.mul_sum, Matrix.trace_sum, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm, Matrix.of_apply]
  rw [h1, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]

theorem solve_system {V : Type*} [AddCommGroup V] [Module S V]
    (D Dinv : Matrix κ κ S) (hDinv : Dinv * D = 1) (v rhs : κ → V)
    (hsys : ∀ a, ∑ b, D a b • v b = rhs a) (c : κ) :
    v c = ∑ a, Dinv c a • rhs a := by
  have h1 : ∑ a, Dinv c a • rhs a = ∑ a, Dinv c a • ∑ b, D a b • v b :=
    Finset.sum_congr rfl fun a _ => by rw [hsys a]
  rw [h1]
  have h2 : ∀ a, Dinv c a • ∑ b, D a b • v b = ∑ b, (Dinv c a * D a b) • v b := by
    intro a
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun a _ => h2 a, Finset.sum_comm]
  have h3 : ∀ b, ∑ a, (Dinv c a * D a b) • v b = ((Dinv * D) c b) • v b := by
    intro b
    rw [← Finset.sum_smul, Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun b _ => h3 b, hDinv]
  simp [Matrix.one_apply]

theorem matrix_mem_smul_top {I : Ideal S} {X : Matrix m m S} (hX : ∀ j l, X j l ∈ I) :
    X ∈ I • (⊤ : Submodule S (Matrix m m S)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ => ?_
  have : Matrix.single j l (X j l) = X j l • Matrix.single j l (1 : S) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (hX j l) Submodule.mem_top

theorem map_finset_sum {α β : Type*} [AddCommMonoid α] [AddCommMonoid β] {p q σ : Type*}
    {F : Type*} [FunLike F α β] [AddMonoidHomClass F α β] (f : F) (s : Finset σ)
    (X : σ → Matrix p q α) : (∑ a ∈ s, X a).map f = ∑ a ∈ s, (X a).map f := by
  ext j l
  simp only [Matrix.map_apply, Matrix.sum_apply, map_sum]

theorem isUnit_det_of_map_residue_eq_one {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Matrix m m A} (hP : P.map (residue A) = 1) : IsUnit P.det := by
  rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hP, det_one]
  exact one_ne_zero

end Generic

section Setting

variable {T : Type} [CommRing T] [IsLocalRing T]
variable {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
  [∀ i, Algebra T (A i)] [∀ i, IsLocalHom (algebraMap T (A i))]
variable {m : Type} [Fintype m] [DecidableEq m]
variable {G : Type*} [Monoid G]

def prodHom (R : ∀ i, G →* Matrix m m (A i)) : G →* Matrix m m (∀ i, A i) where
  toFun g := Matrix.of fun j l i => R i g j l
  map_one' := by
    ext j l i
    simp only [Matrix.of_apply, map_one, Matrix.one_apply]
    split_ifs <;> rfl
  map_mul' g h := by
    ext j l i
    simp only [Matrix.of_apply, map_mul, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply]

@[scoped simp] theorem prodHom_apply (R : ∀ i, G →* Matrix m m (A i)) (g : G) (j l : m) (i : ι) :
    prodHom R g j l i = R i g j l := rfl

theorem prodHom_map_eval (R : ∀ i, G →* Matrix m m (A i)) (g : G) (i : ι) :
    (prodHom R g).map (Pi.evalRingHom A i) = R i g := by
  ext j l; rfl

theorem algebraMap_pi_apply (t : T) (i : ι) :
    algebraMap T (∀ i, A i) t i = algebraMap T (A i) t := rfl

theorem nonempty_index (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0) :
    Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact one_ne_zero (hinj 1 fun i => (IsEmpty.false i).elim)

theorem injective_algebraMap_pi (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0) :
    Function.Injective (algebraMap T (∀ i, A i)) := by
  intro x y hxy
  rw [← sub_eq_zero]
  refine hinj _ fun i => ?_
  have := congrFun hxy i
  rw [algebraMap_pi_apply, algebraMap_pi_apply] at this
  rw [map_sub, this, sub_self]

theorem injective_map_algebraMap_pi
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0) {p q : Type*}
    {X Y : Matrix p q T} (h : X.map (algebraMap T (∀ i, A i)) = Y.map (algebraMap T (∀ i, A i))) :
    X = Y := by
  ext j l
  exact injective_algebraMap_pi hinj (by
    have := congrFun (congrFun h j) l
    simpa only [Matrix.map_apply] using this)

theorem mem_maximalIdeal_of_apply {t : T} (i : ι) (h : algebraMap T (A i) t ∈ maximalIdeal (A i)) :
    t ∈ maximalIdeal T := by
  by_contra ht
  exact (notMem_maximalIdeal.mpr ((notMem_maximalIdeal.mp ht).map (algebraMap T (A i)))) h

end Setting

structure Datum (T : Type) [CommRing T] [IsLocalRing T] {ι : Type} (A : ι → Type)
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)] [∀ i, Algebra T (A i)]
    [∀ i, IsLocalHom (algebraMap T (A i))]
    (m : Type) [Fintype m] [DecidableEq m] (G : Type*) [Monoid G] (κ : Type) [Fintype κ] where
  R : G →* Matrix m m (∀ i, A i)
  Rbar : G →* Matrix m m (ResidueField T)
  τ : G → T
  gg : κ → G
  b₀ : Module.Basis κ (ResidueField T) (Matrix m m (ResidueField T))
  hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0
  hred : ∀ g j l i, residue (A i) (R g j l i) = ResidueField.map (algebraMap T (A i)) (Rbar g j l)
  htr : ∀ g, (R g).trace = algebraMap T (∀ i, A i) (τ g)
  hb₀ : ∀ a, b₀ a = Rbar (gg a)

namespace Datum

variable {T : Type} [CommRing T] [IsLocalRing T]
variable {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
  [∀ i, Algebra T (A i)] [∀ i, IsLocalHom (algebraMap T (A i))]
variable {m : Type} [Fintype m] [DecidableEq m]
variable {G : Type*} [Monoid G] {κ : Type} [Fintype κ] [DecidableEq κ]
set_option quotPrecheck false in
local notation "k" => ResidueField T
set_option quotPrecheck false in
local notation "𝔸" => (∀ i, A i)
set_option quotPrecheck false in
local notation "φ" => algebraMap T (∀ i, A i)

theorem nonempty (D : Datum T A m G κ) : Nonempty ι := nonempty_index D.hinj

theorem φ_injective (D : Datum T A m G κ) : Function.Injective φ := injective_algebraMap_pi D.hinj

variable (D : Datum T A m G κ)

theorem residue_τ (g : G) : residue T (D.τ g) = (D.Rbar g).trace := by
  obtain ⟨i⟩ := D.nonempty
  apply (ResidueField.map (algebraMap T (A i))).injective
  rw [ResidueField.map_residue, ← algebraMap_pi_apply, ← D.htr g, AddMonoidHom.map_trace,
    Matrix.trace, Matrix.trace, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.map_apply]
  exact D.hred g j j i

def Q : Matrix κ κ T := Matrix.of fun a b => D.τ (D.gg a * D.gg b)

theorem Q_map_φ : D.Q.map φ = Matrix.of fun a b => (D.R (D.gg a) * D.R (D.gg b)).trace := by
  ext a b i
  rw [Matrix.map_apply, Matrix.of_apply, Q, Matrix.of_apply, ← map_mul, D.htr]

theorem Q_map_residue :
    D.Q.map (residue T) = Matrix.of fun a b => (D.b₀ a * D.b₀ b).trace := by
  ext a b
  rw [Matrix.map_apply, Matrix.of_apply, Q, Matrix.of_apply, D.residue_τ, map_mul, D.hb₀, D.hb₀]

theorem det_Q_map_residue_ne_zero : (D.Q.map (residue T)).det ≠ 0 := by
  rw [Q_map_residue]
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Y : Matrix m m k := ∑ b, x b • D.b₀ b with hY
  have hYtr : ∀ a, (D.b₀ a * Y).trace = 0 := by
    intro a
    have h3 : (D.b₀ a * Y).trace = ∑ b, (D.b₀ a * D.b₀ b).trace * x b := by
      rw [hY, Finset.mul_sum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm]
    rw [h3]
    exact congrFun hx a
  have hYzero : Y = 0 := by
    rw [Matrix.ext_iff_trace_mul_left]
    intro Z
    have hZ : Z ∈ Submodule.span k (Set.range D.b₀) := D.b₀.span_eq.symm ▸ Submodule.mem_top
    rw [mul_zero, Matrix.trace_zero]
    induction hZ using Submodule.span_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact hYtr a
    | zero => simp
    | add z w _ _ hz hw => rw [add_mul, Matrix.trace_add, hz, hw, add_zero]
    | smul c z _ hz => rw [smul_mul_assoc, Matrix.trace_smul, hz, smul_zero]
  exact hx0 (funext fun b => linearIndependent_iff'.mp D.b₀.linearIndependent Finset.univ x
    (by rw [← hY, hYzero]) b (Finset.mem_univ b))

theorem isUnit_det_Q : IsUnit D.Q.det := by
  rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
  exact D.det_Q_map_residue_ne_zero

theorem Qinv_mul : D.Q⁻¹ * D.Q = 1 := Matrix.nonsing_inv_mul _ D.isUnit_det_Q

theorem mul_Qinv : D.Q * D.Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ D.isUnit_det_Q

theorem Qinv_map {S : Type*} [CommRing S] (f : T →+* S) : (D.Q.map f)⁻¹ = D.Q⁻¹.map f :=
  Matrix.inv_eq_right_inv (by rw [← Matrix.map_mul, D.mul_Qinv, Matrix.map_one _ (map_zero f) (map_one f)])

theorem Qinv_map_mul {S : Type*} [CommRing S] (f : T →+* S) : D.Q⁻¹.map f * D.Q.map f = 1 := by
  rw [← Matrix.map_mul, D.Qinv_mul, Matrix.map_one _ (map_zero f) (map_one f)]

def Ψ : (κ → T) →ₗ[T] Matrix m m 𝔸 where
  toFun t := ∑ a, φ (t a) • D.R (D.gg a)
  map_add' s t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [Pi.add_apply, map_add, add_smul]
  map_smul' c t := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, mul_smul, algebraMap_smul]

theorem Ψ_apply (t : κ → T) : D.Ψ t = ∑ a, φ (t a) • D.R (D.gg a) := rfl

def d (g : G) : κ → T := D.Q⁻¹.mulVec fun b => D.τ (D.gg b * g)

theorem span_eval_eq_top (i : ι) :
    Submodule.span (A i) (Set.range fun a => (D.R (D.gg a)).map (Pi.evalRingHom A i)) = ⊤ := by
  set N := Submodule.span (A i) (Set.range fun a => (D.R (D.gg a)).map (Pi.evalRingHom A i))
  set kA := ResidueField (A i)
  set ψ := ResidueField.map (algebraMap T (A i))

  have hbar : ∀ Y : Matrix m m kA, ∃ c : κ → A i,
      Y = (∑ a, c a • (D.R (D.gg a)).map (Pi.evalRingHom A i)).map (residue (A i)) := by

    have hsingle : ∀ (j l : m), ∃ c : κ → kA,
        Matrix.single j l (1 : kA) = ∑ a, c a • (D.b₀ a).map ψ := by
      intro j l
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp
        (show Matrix.single j l (1 : k) ∈ Submodule.span k (Set.range D.b₀) from
          D.b₀.span_eq.symm ▸ Submodule.mem_top)
      refine ⟨fun a => ψ (c a), ?_⟩
      have : Matrix.single j l (1 : kA) = (Matrix.single j l (1 : k)).map ψ := by
        ext j' l'
        simp only [Matrix.map_apply, Matrix.single, Matrix.of_apply]
        split_ifs <;> simp
      rw [this, ← hc, map_finset_sum ψ]
      exact Finset.sum_congr rfl fun a _ => by rw [Matrix.map_smul' _ _ _ (map_mul ψ)]
    intro Y
    choose c hc using hsingle

    have hY : Y = ∑ a, (∑ j, ∑ l, Y j l * c j l a) • (D.b₀ a).map ψ := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      have h1 : ∀ j l, Matrix.single j l (Y j l) = ∑ a, (Y j l * c j l a) • (D.b₀ a).map ψ := by
        intro j l
        rw [show Matrix.single j l (Y j l) = Y j l • Matrix.single j l (1 : kA) by
          rw [Matrix.smul_single, smul_eq_mul, mul_one], hc j l, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => by rw [smul_smul]
      simp_rw [h1]
      symm
      calc ∑ a, (∑ j, ∑ l, Y j l * c j l a) • (D.b₀ a).map ψ
          = ∑ a, ∑ j, ∑ l, (Y j l * c j l a) • (D.b₀ a).map ψ :=
            Finset.sum_congr rfl fun a _ => by
              rw [Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => Finset.sum_smul
        _ = ∑ j, ∑ a, ∑ l, (Y j l * c j l a) • (D.b₀ a).map ψ := Finset.sum_comm
        _ = ∑ j, ∑ l, ∑ a, (Y j l * c j l a) • (D.b₀ a).map ψ :=
            Finset.sum_congr rfl fun j _ => Finset.sum_comm

    choose c' hc' using fun a => residue_surjective (R := A i) (∑ j, ∑ l, Y j l * c j l a)
    refine ⟨c', ?_⟩
    rw [hY, map_finset_sum (residue (A i))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.map_smul' _ _ _ (map_mul (residue (A i))), hc' a, Matrix.map_map]
    congr 1
    ext j l
    simp only [Matrix.map_apply, Function.comp_apply, Pi.evalRingHom_apply]
    rw [D.hred, D.hb₀]

  haveI : Module.Finite (A i) (Matrix m m (A i)) := inferInstance
  rw [← IsLocalRing.map_mkQ_eq_top (N := N), Submodule.map_mkQ_eq_top, eq_top_iff]
  rintro Y -
  obtain ⟨c, hc⟩ := hbar (Y.map (residue (A i)))
  set Z := ∑ a, c a • (D.R (D.gg a)).map (Pi.evalRingHom A i) with hZ
  have hZN : Z ∈ N := Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hdiff : Y - Z ∈ maximalIdeal (A i) • (⊤ : Submodule (A i) (Matrix m m (A i))) := by
    refine matrix_mem_smul_top fun j l => ?_
    rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
    have := congrFun (congrFun hc j) l
    rwa [Matrix.map_apply, Matrix.map_apply] at this
  rw [show Y = (Y - Z) + Z by abel]
  exact Submodule.add_mem_sup hdiff hZN

theorem exists_eq_sum_smul (X : Matrix m m 𝔸) : ∃ c : κ → 𝔸, X = ∑ a, c a • D.R (D.gg a) := by
  have h : ∀ i, ∃ c : κ → A i,
      X.map (Pi.evalRingHom A i) = ∑ a, c a • (D.R (D.gg a)).map (Pi.evalRingHom A i) := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (A i)).mp
      (show X.map (Pi.evalRingHom A i) ∈ _ from (D.span_eval_eq_top i).symm ▸ Submodule.mem_top)
    exact ⟨c, hc.symm⟩
  choose c hc using h
  refine ⟨fun a i => c i a, ?_⟩
  ext j l i
  have := congrFun (congrFun (hc i) j) l
  simp only [Matrix.map_apply, Pi.evalRingHom_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] at this
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.mul_apply]
  exact this

def coordA (X : Matrix m m 𝔸) : κ → 𝔸 :=
  (D.Q⁻¹.map φ).mulVec fun b => (D.R (D.gg b) * X).trace

theorem coordA_eq_of_eq_sum {X : Matrix m m 𝔸} {c : κ → 𝔸} (hX : X = ∑ a, c a • D.R (D.gg a)) :
    D.coordA X = c :=
  gram_solve _ _ (by rw [← D.Q_map_φ, D.Qinv_map_mul]) c X hX

theorem eq_sum_coordA_smul (X : Matrix m m 𝔸) : X = ∑ a, D.coordA X a • D.R (D.gg a) := by
  obtain ⟨c, hc⟩ := D.exists_eq_sum_smul X
  rw [D.coordA_eq_of_eq_sum hc]
  exact hc

theorem coordA_Ψ (t : κ → T) : D.coordA (D.Ψ t) = φ ∘ t :=
  D.coordA_eq_of_eq_sum rfl

theorem Ψ_injective : Function.Injective D.Ψ := by
  intro s t h
  have := congrArg D.coordA h
  rw [D.coordA_Ψ, D.coordA_Ψ] at this
  exact funext fun a => D.φ_injective (congrFun this a)

theorem R_eq_Ψ_d (g : G) : D.R g = D.Ψ (D.d g) := by
  have hc : D.coordA (D.R g) = φ ∘ D.d g := by
    funext a
    rw [coordA, Function.comp_apply, d, RingHom.map_mulVec]
    congr 1
    funext b
    rw [Function.comp_apply, ← map_mul, D.htr]
  rw [Ψ_apply]
  conv_lhs => rw [D.eq_sum_coordA_smul (D.R g), hc]
  rfl

theorem d_gg (a : κ) : D.d (D.gg a) = Pi.single a 1 := by
  apply D.Ψ_injective
  rw [← R_eq_Ψ_d, Ψ_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ a)).elim), Pi.single_eq_same, map_one, one_smul]

theorem Ψ_one_eq : D.Ψ (D.d 1) = 1 := by rw [← R_eq_Ψ_d, map_one]

def mulT (s t : κ → T) : κ → T := ∑ a, ∑ b, (s a * t b) • D.d (D.gg a * D.gg b)

theorem mulT_apply (s t : κ → T) (c : κ) :
    D.mulT s t c = ∑ a, ∑ b, s a * t b * D.d (D.gg a * D.gg b) c := by
  simp only [mulT, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem Ψ_mulT (s t : κ → T) : D.Ψ (D.mulT s t) = D.Ψ s * D.Ψ t := by
  rw [mulT, map_sum]
  simp_rw [map_sum, LinearMap.map_smul, ← R_eq_Ψ_d, map_mul]
  rw [Ψ_apply, Ψ_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← map_mul (algebraMap T (∀ i, A i)),
    algebraMap_smul]

theorem Ψ_eq_iff {s t : κ → T} : D.Ψ s = D.Ψ t ↔ s = t := D.Ψ_injective.eq_iff

theorem mulT_assoc (s t u : κ → T) : D.mulT (D.mulT s t) u = D.mulT s (D.mulT t u) := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, mul_assoc]

theorem mulT_one (s : κ → T) : D.mulT s (D.d 1) = s := by
  rw [← D.Ψ_eq_iff, Ψ_mulT, Ψ_one_eq, mul_one]

theorem one_mulT (s : κ → T) : D.mulT (D.d 1) s = s := by
  rw [← D.Ψ_eq_iff, Ψ_mulT, Ψ_one_eq, one_mul]

theorem mulT_add (s t u : κ → T) : D.mulT s (t + u) = D.mulT s t + D.mulT s u := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, map_add, mul_add]

theorem add_mulT (s t u : κ → T) : D.mulT (s + t) u = D.mulT s u + D.mulT t u := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, map_add, add_mul]

theorem mulT_sub (s t u : κ → T) : D.mulT s (t - u) = D.mulT s t - D.mulT s u := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, map_sub, mul_sub]

theorem sub_mulT (s t u : κ → T) : D.mulT (s - t) u = D.mulT s u - D.mulT t u := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, map_sub, sub_mul]

theorem mulT_smul (c : T) (s t : κ → T) : D.mulT s (c • t) = c • D.mulT s t := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, LinearMap.map_smul, mul_smul_comm]

theorem smul_mulT (c : T) (s t : κ → T) : D.mulT (c • s) t = c • D.mulT s t := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, LinearMap.map_smul, smul_mul_assoc]

theorem sum_mulT {σ : Type*} (S : Finset σ) (f : σ → κ → T) (t : κ → T) :
    D.mulT (∑ x ∈ S, f x) t = ∑ x ∈ S, D.mulT (f x) t := by
  rw [← D.Ψ_eq_iff]; simp only [Ψ_mulT, map_sum, Finset.sum_mul]

theorem d_mul (g h : G) : D.d (g * h) = D.mulT (D.d g) (D.d h) := by
  rw [← D.Ψ_eq_iff, Ψ_mulT, ← R_eq_Ψ_d, ← R_eq_Ψ_d, ← R_eq_Ψ_d, map_mul]

theorem eq_sum_smul_d (s : κ → T) : s = ∑ a, s a • D.d (D.gg a) := by
  simp_rw [d_gg]
  ext c
  simp [Finset.sum_apply, Pi.single_apply]

theorem mulT_mem_of_left {I : Ideal T} {s : κ → T} (hs : ∀ a, s a ∈ I) (t : κ → T) (c : κ) :
    D.mulT s t c ∈ I := by
  rw [mulT_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (hs a))

theorem mulT_mem_of_right {I : Ideal T} (s : κ → T) {t : κ → T} (ht : ∀ a, t a ∈ I) (c : κ) :
    D.mulT s t c ∈ I := by
  rw [mulT_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (ht b))

theorem mulT_mem_mul {I J : Ideal T} {s t : κ → T} (hs : ∀ a, s a ∈ I) (ht : ∀ a, t a ∈ J)
    (c : κ) : D.mulT s t c ∈ I * J := by
  rw [mulT_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hs a) (ht b))

def red (t : κ → T) : Matrix m m k := D.b₀.equivFun.symm fun a => residue T (t a)

theorem red_apply (t : κ → T) : D.red t = ∑ a, residue T (t a) • D.b₀ a :=
  D.b₀.equivFun_symm_apply _

theorem red_entry (t : κ → T) (j l : m) : D.red t j l = ∑ a, residue T (t a) * D.b₀ a j l := by
  simp only [red_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

def redHom : (κ → T) →ₛₗ[residue T] Matrix m m k where
  toFun := D.red
  map_add' s t := by
    simp only [red_apply, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by
    simp only [red_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

@[scoped simp] theorem redHom_apply (t : κ → T) : D.redHom t = D.red t := rfl

theorem red_add (s t : κ → T) : D.red (s + t) = D.red s + D.red t := map_add D.redHom s t
theorem red_sub (s t : κ → T) : D.red (s - t) = D.red s - D.red t := map_sub D.redHom s t
theorem red_smul (c : T) (t : κ → T) : D.red (c • t) = residue T c • D.red t :=
  D.redHom.map_smulₛₗ c t
theorem red_sum {σ : Type*} (S : Finset σ) (f : σ → κ → T) :
    D.red (∑ x ∈ S, f x) = ∑ x ∈ S, D.red (f x) := map_sum D.redHom f S

theorem red_eq_zero_iff (t : κ → T) : D.red t = 0 ↔ ∀ a, t a ∈ maximalIdeal T := by
  rw [red, LinearEquiv.map_eq_zero_iff, funext_iff]
  exact forall_congr' fun a => residue_eq_zero_iff (t a)

theorem exists_red_eq (Z : Matrix m m k) : ∃ t : κ → T, D.red t = Z := by
  choose t ht using fun a => residue_surjective (R := T) (D.b₀.equivFun Z a)
  refine ⟨t, ?_⟩
  rw [red, show (fun a => residue T (t a)) = D.b₀.equivFun Z from funext ht,
    LinearEquiv.symm_apply_apply]

theorem red_d (g : G) : D.red (D.d g) = D.Rbar g := by
  rw [red, LinearEquiv.symm_apply_eq, Module.Basis.equivFun_apply]

  have h1 : (fun a => residue T (D.d g a)) =
      (D.Q.map (residue T))⁻¹.mulVec fun b => (D.b₀ b * D.Rbar g).trace := by
    funext a
    rw [d, RingHom.map_mulVec, D.Qinv_map]
    congr 1
    funext b
    rw [Function.comp_apply, D.residue_τ, map_mul, D.hb₀]
  rw [h1]
  exact gram_solve _ _ (by rw [← D.Q_map_residue, D.Qinv_map, D.Qinv_map_mul]) _ _
    (D.b₀.sum_repr (D.Rbar g)).symm

theorem red_one : D.red (D.d 1) = 1 := by rw [red_d, map_one]

theorem red_mulT (s t : κ → T) : D.red (D.mulT s t) = D.red s * D.red t := by
  rw [mulT, red_sum]
  simp_rw [red_sum, red_smul, red_d, map_mul, ← D.hb₀]
  rw [red_apply, red_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

theorem residue_Ψ_entry (t : κ → T) (j l : m) (i : ι) :
    residue (A i) (D.Ψ t j l i) = ResidueField.map (algebraMap T (A i)) (D.red t j l) := by
  rw [Ψ_apply, red_entry, map_sum]
  simp only [Matrix.sum_apply, Finset.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.mul_apply,
    map_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [algebraMap_pi_apply, ← ResidueField.map_residue, D.hred, D.hb₀]

theorem newton_identity {S : Type*} [Ring S] (e : S) :
    (3 * e ^ 2 - 2 * e ^ 3) ^ 2 - (3 * e ^ 2 - 2 * e ^ 3) =
      ((e ^ 2 - e) * (e ^ 2 - e)) * (4 * (e ^ 2 - e) - 3) := by
  have h := congrArg (Polynomial.aeval e)
    (show ((3 : Polynomial ℤ) * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3) ^ 2 -
        (3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3) =
      ((Polynomial.X ^ 2 - Polynomial.X) * (Polynomial.X ^ 2 - Polynomial.X)) *
        (4 * (Polynomial.X ^ 2 - Polynomial.X) - 3) from by ring)
  simpa only [map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X] using h

def defect (t : κ → T) : κ → T := D.mulT t t - t

theorem Ψ_defect (t : κ → T) : D.Ψ (D.defect t) = D.Ψ t ^ 2 - D.Ψ t := by
  rw [defect, map_sub, Ψ_mulT, pow_two]

def newton (t₀ : κ → T) : ℕ → (κ → T)
  | 0 => t₀
  | n + 1 =>
    (D.mulT (newton t₀ n) (newton t₀ n) + D.mulT (newton t₀ n) (newton t₀ n) +
        D.mulT (newton t₀ n) (newton t₀ n)) -
      (D.mulT (newton t₀ n) (D.mulT (newton t₀ n) (newton t₀ n)) +
        D.mulT (newton t₀ n) (D.mulT (newton t₀ n) (newton t₀ n)))

theorem Ψ_newton_succ (t₀ : κ → T) (n : ℕ) :
    D.Ψ (D.newton t₀ (n + 1)) = 3 * D.Ψ (D.newton t₀ n) ^ 2 - 2 * D.Ψ (D.newton t₀ n) ^ 3 := by
  show D.Ψ ((D.mulT _ _ + D.mulT _ _ + D.mulT _ _) - (D.mulT _ _ + D.mulT _ _)) = _
  simp only [map_sub, map_add, Ψ_mulT]
  noncomm_ring

theorem defect_newton_succ (t₀ : κ → T) (n : ℕ) :
    D.defect (D.newton t₀ (n + 1)) =
      D.mulT (D.mulT (D.defect (D.newton t₀ n)) (D.defect (D.newton t₀ n)))
        ((D.defect (D.newton t₀ n) + D.defect (D.newton t₀ n) + D.defect (D.newton t₀ n) +
          D.defect (D.newton t₀ n)) - (D.d 1 + D.d 1 + D.d 1)) := by
  rw [← D.Ψ_eq_iff, Ψ_defect, Ψ_newton_succ, newton_identity]
  simp only [Ψ_mulT, map_sub, map_add, Ψ_defect, Ψ_one_eq]
  noncomm_ring

theorem newton_succ_sub (t₀ : κ → T) (n : ℕ) :
    D.newton t₀ (n + 1) - D.newton t₀ n =
      D.mulT (D.defect (D.newton t₀ n)) (D.d 1 - (D.newton t₀ n + D.newton t₀ n)) := by
  rw [← D.Ψ_eq_iff, map_sub, Ψ_newton_succ, Ψ_mulT, Ψ_defect, map_sub, map_add, Ψ_one_eq]
  noncomm_ring

theorem defect_newton_mem (t₀ : κ → T) (h0 : ∀ a, D.defect t₀ a ∈ maximalIdeal T) (n : ℕ)
    (a : κ) : D.defect (D.newton t₀ n) a ∈ maximalIdeal T ^ (n + 1) := by
  induction n generalizing a with
  | zero => rw [zero_add, pow_one]; exact h0 a
  | succ n ih =>
    rw [defect_newton_succ]
    refine D.mulT_mem_of_left (fun c => ?_) _ a
    have h := D.mulT_mem_mul ih ih c
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h

theorem newton_succ_sub_mem (t₀ : κ → T) (h0 : ∀ a, D.defect t₀ a ∈ maximalIdeal T) (n : ℕ)
    (a : κ) : D.newton t₀ (n + 1) a - D.newton t₀ n a ∈ maximalIdeal T ^ (n + 1) := by
  rw [← Pi.sub_apply, newton_succ_sub]
  exact D.mulT_mem_of_left (D.defect_newton_mem t₀ h0 n) _ a

theorem newton_sub_mem (t₀ : κ → T) (h0 : ∀ a, D.defect t₀ a ∈ maximalIdeal T) {p q : ℕ}
    (hpq : p ≤ q) (a : κ) : D.newton t₀ q a - D.newton t₀ p a ∈ maximalIdeal T ^ p := by
  induction q, hpq using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ q hq ih =>
    have h1 := D.newton_succ_sub_mem t₀ h0 q a
    rw [show D.newton t₀ (q + 1) a - D.newton t₀ p a =
      (D.newton t₀ (q + 1) a - D.newton t₀ q a) + (D.newton t₀ q a - D.newton t₀ p a) by abel]
    exact Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) h1) ih

theorem exists_mulT_self_eq [IsAdicComplete (maximalIdeal T) T] (t₀ : κ → T)
    (h0 : ∀ a, D.defect t₀ a ∈ maximalIdeal T) :
    ∃ t : κ → T, D.mulT t t = t ∧ ∀ a, t a - t₀ a ∈ maximalIdeal T := by

  have hlim : ∀ a, ∃ L : T, ∀ n, D.newton t₀ n a ≡ L
      [SMOD (maximalIdeal T ^ n • ⊤ : Submodule T T)] := by
    intro a
    refine IsPrecomplete.prec' (fun n => D.newton t₀ n a) fun {p q} hpq => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, Ideal.neg_mem_iff]
    exact D.newton_sub_mem t₀ h0 hpq a
  choose L hL using hlim
  have hLmem : ∀ n a, L a - D.newton t₀ n a ∈ maximalIdeal T ^ n := by
    intro n a
    have := (hL a n).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  refine ⟨L, ?_, fun a => ?_⟩
  ·
    refine funext fun a => ?_
    rw [← sub_eq_zero, ← Pi.sub_apply]
    refine IsHausdorff.haus' (I := maximalIdeal T) _ fun n => ?_
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    set x := D.newton t₀ n
    set e := L - x with he
    have hkey : D.mulT L L - L = D.defect x + (D.mulT x e + D.mulT e L - e) := by
      have hL' : L = x + e := by rw [he]; abel
      rw [← D.Ψ_eq_iff]
      simp only [map_sub, map_add, Ψ_mulT, Ψ_defect]
      rw [hL', map_add]
      noncomm_ring
    rw [hkey, Pi.add_apply, Pi.sub_apply, Pi.add_apply]
    have hea : ∀ c, e c ∈ maximalIdeal T ^ n := fun c => hLmem n c
    refine Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) (D.defect_newton_mem t₀ h0 n a))
      (Ideal.sub_mem _ (Ideal.add_mem _ (D.mulT_mem_of_right _ hea a) (D.mulT_mem_of_left hea _ a))
        (hea a))
  · have h1 : L a - D.newton t₀ 1 a ∈ maximalIdeal T := by
      have := hLmem 1 a; rwa [pow_one] at this
    have h2 : D.newton t₀ 1 a - D.newton t₀ 0 a ∈ maximalIdeal T := by
      have := D.newton_succ_sub_mem t₀ h0 0 a; rwa [zero_add, pow_one] at this
    have : L a - t₀ a = (L a - D.newton t₀ 1 a) + (D.newton t₀ 1 a - D.newton t₀ 0 a) := by
      show L a - t₀ a = (L a - D.newton t₀ 1 a) + (D.newton t₀ 1 a - t₀ a)
      abel
    rw [this]
    exact Ideal.add_mem _ h1 h2

theorem exists_mulT_self_eq_and_red_eq [IsAdicComplete (maximalIdeal T) T] {E : Matrix m m k}
    (hE : E * E = E) : ∃ t : κ → T, D.mulT t t = t ∧ D.red t = E := by
  obtain ⟨t₀, ht₀⟩ := D.exists_red_eq E
  have h0 : ∀ a, D.defect t₀ a ∈ maximalIdeal T := by
    rw [← D.red_eq_zero_iff, defect, red_sub, red_mulT, ht₀, hE, sub_self]
  obtain ⟨t, ht, htt₀⟩ := D.exists_mulT_self_eq t₀ h0
  refine ⟨t, ht, ?_⟩
  rw [← sub_eq_zero, ← ht₀, ← red_sub, D.red_eq_zero_iff]
  exact htt₀

theorem exists_eq_sum_smul_of_mulT_eq (i₀ : m) {cε : κ → T} (hε : D.mulT cε cε = cε)
    (hεred : D.red cε = Matrix.single i₀ i₀ 1) {cw : m → κ → T}
    (hwε : ∀ j, D.mulT (cw j) cε = cw j) (hwred : ∀ j, D.red (cw j) = Matrix.single j i₀ 1) :
    ∀ cZ : κ → T, D.mulT cZ cε = cZ → ∃ t : m → T, cZ = ∑ j, t j • cw j := by
  classical

  set v : κ → (κ → T) := fun a => D.mulT (D.d (D.gg a)) cε with hv
  have hvε : ∀ a, D.mulT (v a) cε = v a := fun a => by
    show D.mulT (D.mulT (D.d (D.gg a)) cε) cε = D.mulT (D.d (D.gg a)) cε
    rw [mulT_assoc, hε]
  have hmulε : ∀ u : κ → T, D.mulT u cε = ∑ a, u a • v a := fun u => by
    conv_lhs => rw [D.eq_sum_smul_d u]
    rw [sum_mulT]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_mulT]

  have step1 : ∀ cZ, D.mulT cZ cε = cZ → ∃ (t : m → T) (u : κ → T),
      (∀ a, u a ∈ maximalIdeal T) ∧ cZ = (∑ j, t j • cw j) + ∑ a, u a • v a := by
    intro cZ hZε
    set Zbar := D.red cZ with hZbar
    have hZbarε : Zbar * Matrix.single i₀ i₀ (1 : k) = Zbar := by
      rw [hZbar, ← hεred, ← red_mulT, hZε]

    choose t ht using fun j => residue_surjective (R := T) (Zbar j i₀)
    have hdiff : D.red (cZ - ∑ j, t j • cw j) = 0 := by
      rw [red_sub, red_sum, sub_eq_zero]
      simp_rw [red_smul, hwred, ht]
      ext i' j'
      rw [Matrix.sum_apply]
      by_cases hj' : j' = i₀
      · subst hj'
        rw [show ∑ j, (Zbar j j' • Matrix.single j j' (1 : k)) i' j' =
            ∑ j, if j = i' then Zbar j j' else 0 from
          Finset.sum_congr rfl fun j _ => by
            simp only [Matrix.smul_apply, Matrix.single, Matrix.of_apply, smul_eq_mul, mul_ite,
              mul_one, mul_zero, and_true]]
        rw [Finset.sum_ite_eq' Finset.univ i' fun j => Zbar j j']
        simp [hZbar]
      · rw [show ∑ j, (Zbar j i₀ • Matrix.single j i₀ (1 : k)) i' j' = 0 from
          Finset.sum_eq_zero fun j _ => by
            rw [Matrix.smul_apply, Matrix.single_apply_of_col_ne _ _ (Ne.symm hj'), smul_zero]]
        calc Zbar i' j' = (Zbar * Matrix.single i₀ i₀ (1 : k)) i' j' := by rw [hZbarε]
          _ = 0 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_eq_zero fun x _ => by
              rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj'), mul_zero]
    set u := cZ - ∑ j, t j • cw j with hu
    have hum : ∀ a, u a ∈ maximalIdeal T := (D.red_eq_zero_iff u).mp hdiff
    refine ⟨t, u, hum, ?_⟩
    have h5 : D.mulT u cε = u := by
      rw [hu, sub_mulT, hZε, sum_mulT]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mulT, hwε]
    rw [← hmulε u, h5, hu]
    abel

  choose s uu huum hveq using fun a => step1 (v a) (hvε a)
  set Dm : Matrix κ κ T := 1 - Matrix.of fun a b => uu a b with hDm
  have hDab : ∀ a b, Dm a b = (if a = b then (1 : T) else 0) - uu a b := fun a b => by
    rw [hDm, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
  have hDdet : IsUnit Dm.det := by
    refine isUnit_det_of_map_residue_eq_one ?_
    ext a b
    rw [Matrix.map_apply, hDab, map_sub, (residue_eq_zero_iff _).mpr (huum a b), sub_zero,
      Matrix.one_apply]
    split_ifs <;> simp
  have hDinvD : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hDdet
  have hsys : ∀ a, ∑ b, Dm a b • v b = ∑ j, s a j • cw j := by
    intro a
    have h1 : ∀ b, Dm a b • v b = (if a = b then (1 : T) else 0) • v b - uu a b • v b :=
      fun b => by rw [hDab a b, sub_smul]
    rw [Finset.sum_congr rfl fun b _ => h1 b, Finset.sum_sub_distrib]
    have h3 : ∑ b, (if a = b then (1 : T) else 0) • v b = v a := by
      simp [Finset.sum_ite_eq]
    rw [h3]
    conv_lhs => rw [hveq a]
    abel
  have hvsol : ∀ c, v c = ∑ a, Dm⁻¹ c a • ∑ j, s a j • cw j :=
    fun c => solve_system Dm Dm⁻¹ hDinvD v (fun a => ∑ j, s a j • cw j) hsys c
  have hvw : ∀ c, ∃ e : m → T, v c = ∑ j, e j • cw j := by
    intro c
    refine ⟨fun j => ∑ a, Dm⁻¹ c a * s a j, ?_⟩
    rw [hvsol c]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) =>
      (Finset.smul_sum (r := Dm⁻¹ c a) (f := fun j => s a j • cw j) (s := Finset.univ))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _

  intro cZ hZε
  obtain ⟨t, u, -, hZeq⟩ := step1 cZ hZε
  choose e heq using hvw
  refine ⟨fun j => t j + ∑ a, u a * e a j, ?_⟩
  rw [hZeq]
  have h8 : ∀ a, u a • v a = ∑ j, (u a * e a j) • cw j := fun a => by
    rw [heq a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => h8 a, Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_smul, Finset.sum_smul]

theorem exists_conj [IsAdicComplete (maximalIdeal T) T] [Nonempty m] :
    ∃ (C : G →* Matrix m m T) (P : Matrix m m 𝔸),
      (∀ j l i, residue (A i) (P j l i) = (1 : Matrix m m (ResidueField (A i))) j l) ∧
      IsUnit P.det ∧ ∀ g, D.R g * P = P * (C g).map φ := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty m›

  have hE : Matrix.single i₀ i₀ (1 : k) * Matrix.single i₀ i₀ 1 = Matrix.single i₀ i₀ 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  obtain ⟨cε, hε, hεred⟩ := D.exists_mulT_self_eq_and_red_eq hE

  choose cW hcW using fun j : m => D.exists_red_eq (Matrix.single j i₀ (1 : k))
  set cw : m → κ → T := fun j => D.mulT (cW j) cε with hcw
  have hwε : ∀ j, D.mulT (cw j) cε = cw j := fun j => by
    show D.mulT (D.mulT (cW j) cε) cε = D.mulT (cW j) cε
    rw [mulT_assoc, hε]
  have hwred : ∀ j, D.red (cw j) = Matrix.single j i₀ 1 := fun j => by
    show D.red (D.mulT (cW j) cε) = _
    rw [red_mulT, hcW, hεred, Matrix.single_mul_single_same, one_mul]
  have hspan := D.exists_eq_sum_smul_of_mulT_eq i₀ hε hεred hwε hwred

  set w : m → Matrix m m 𝔸 := fun j => D.Ψ (cw j) with hw
  set P : Matrix m m 𝔸 := Matrix.of fun j l => w l j i₀ with hP
  have hPred : ∀ j l i, residue (A i) (P j l i) = (1 : Matrix m m (ResidueField (A i))) j l := by
    intro j l i
    show residue (A i) (D.Ψ (cw l) j i₀ i) = _
    rw [residue_Ψ_entry, hwred, Matrix.one_apply]
    simp only [Matrix.single, Matrix.of_apply, and_true]
    by_cases h : l = j
    · subst h
      rw [if_pos rfl, map_one, if_pos rfl]
    · rw [if_neg h, map_zero, if_neg (Ne.symm h)]
  have hPdet : IsUnit P.det := by
    rw [Pi.isUnit_iff]
    intro i
    have : P.det i = (P.map (Pi.evalRingHom A i)).det := by
      rw [← Pi.evalRingHom_apply A i P.det, RingHom.map_det, RingHom.mapMatrix_apply]
    rw [this]
    refine isUnit_det_of_map_residue_eq_one ?_
    ext j l
    rw [Matrix.map_apply, Matrix.map_apply, Pi.evalRingHom_apply, hPred]

  have hcol : ∀ g l, ∃ c : m → T, D.mulT (D.d g) (cw l) = ∑ j, c j • cw j := fun g l =>
    hspan _ (by rw [mulT_assoc, hwε])
  choose c hc using hcol
  set Cf : G → Matrix m m T := fun g => Matrix.of fun j l => c g l j with hCf
  have hcomm : ∀ g, D.R g * P = P * (Cf g).map φ := by
    intro g
    have hcolw : ∀ l, D.R g * w l = ∑ j, φ (c g l j) • w j := fun l => by
      show D.R g * D.Ψ (cw l) = ∑ j, φ (c g l j) • D.Ψ (cw j)
      rw [R_eq_Ψ_d, ← Ψ_mulT, hc, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [LinearMap.map_smul, algebraMap_smul]
    refine Matrix.ext fun i' j' => ?_
    rw [Matrix.mul_apply, Matrix.mul_apply]
    calc ∑ x, D.R g i' x * P x j' = (D.R g * w j') i' i₀ := by rw [Matrix.mul_apply]; rfl
      _ = (∑ j, φ (c g j' j) • w j) i' i₀ := by rw [hcolw j']
      _ = ∑ j, φ (c g j' j) * w j i' i₀ := by
          rw [Matrix.sum_apply]
          exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul]
      _ = ∑ j, P i' j * (Cf g).map φ j j' :=
          Finset.sum_congr rfl fun j _ => by rw [mul_comm]; rfl

  have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hPdet
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hPdet
  have hconj : ∀ g, (Cf g).map φ = P⁻¹ * D.R g * P := fun g => by
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hPinv, Matrix.one_mul]
  have hmul : ∀ g h, Cf (g * h) = Cf g * Cf h := fun g h => by
    apply injective_map_algebraMap_pi D.hinj
    rw [Matrix.map_mul, hconj, hconj, hconj, map_mul]
    symm
    calc P⁻¹ * D.R g * P * (P⁻¹ * D.R h * P) = P⁻¹ * D.R g * (P * P⁻¹) * D.R h * P := by
          simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (D.R g * D.R h) * P := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hone : Cf 1 = 1 := injective_map_algebraMap_pi D.hinj (by
    rw [hconj, map_one, Matrix.mul_one, hPinv, Matrix.map_one _ (map_zero _) (map_one _)])
  exact ⟨{ toFun := Cf, map_one' := hone, map_mul' := hmul }, P, hPred, hPdet, fun g => hcomm g⟩

end Datum
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum"

theorem exists_monoidHom_matrix_forall_mul_eq_mul_map
    {T : Type} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    {ι : Type} (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    {m : Type} [Fintype m] [DecidableEq m] {G : Type*} [Monoid G]
    (Rbar : G →* Matrix m m (ResidueField T))
    (hspan : Submodule.span (ResidueField T) (Set.range ⇑Rbar) = ⊤)
    (R : ∀ i, G →* Matrix m m (A i))
    (hred : ∀ i g j l,
      residue (A i) (R i g j l) = ResidueField.map (algebraMap T (A i)) (Rbar g j l))
    (τ : G → T) (htr : ∀ i g, (R i g).trace = algebraMap T (A i) (τ g)) :
    ∃ (C : G →* Matrix m m T) (P : ∀ i, Matrix m m (A i)),
      (∀ i, (P i).map (residue (A i)) = 1) ∧ (∀ i, IsUnit (P i)) ∧
      ∀ i g, R i g * P i = P i * (C g).map (algebraMap T (A i)) := by
  classical
  rcases isEmpty_or_nonempty m with hm | hm
  · refine ⟨1, fun _ => 1, fun i => Matrix.map_one _ (map_zero _) (map_one _),
      fun i => isUnit_one, fun i g => Subsingleton.elim _ _⟩

  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent (ResidueField T) (Set.range ⇑Rbar)
  haveI : Fintype s := hs_li.setFinite.fintype
  choose f hf using hs_sub
  let b₀ : Module.Basis s (ResidueField T) (Matrix m m (ResidueField T)) :=
    Module.Basis.mk hs_li (by rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hs_span, hspan])
  let D : Datum T A m G s :=
    { R := prodHom R
      Rbar := Rbar
      τ := τ
      gg := fun a => f a.2
      b₀ := b₀
      hinj := hinj
      hred := fun g j l i => hred i g j l
      htr := fun g => by
        funext i
        rw [algebraMap_pi_apply, ← htr i g, Matrix.trace, Matrix.trace, Finset.sum_apply]
        rfl
      hb₀ := fun a => by rw [Module.Basis.mk_apply, hf a.2] }
  obtain ⟨C, P, hPred, hPdet, hcomm⟩ := D.exists_conj
  have hPi : ∀ i, (P.map (Pi.evalRingHom A i)).map (residue (A i)) = 1 := fun i => by
    ext j l
    rw [Matrix.map_apply, Matrix.map_apply, Pi.evalRingHom_apply, hPred]
  refine ⟨C, fun i => P.map (Pi.evalRingHom A i), hPi, fun i => ?_, fun i g => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_det_of_map_residue_eq_one (hPi i)
  · have h := congrArg (fun X : Matrix m m (∀ i, A i) => X.map (Pi.evalRingHom A i)) (hcomm g)
    simp only [Matrix.map_mul] at h
    rw [prodHom_map_eval, Matrix.map_map] at h
    exact h

end CarayolMatrix
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix"

end
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix"

namespace CarayolAsm

open IsLocalRing TensorProduct Matrix

section Models

noncomputable def matrixHom {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    {n : Type} [Fintype n] [DecidableEq n] (b : Module.Basis n A V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix n n A where
  toFun σ := LinearMap.toMatrix b b (ρ σ)
  map_one' := by rw [map_one, LinearMap.toMatrix_one]
  map_mul' σ τ := by rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp b b b]

@[scoped simp] theorem matrixHom_apply {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    {n : Type} [Fintype n] [DecidableEq n] (b : Module.Basis n A V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    matrixHom b ρ σ = LinearMap.toMatrix b b (ρ σ) := rfl

theorem exists_basis_residue_toMatrix_eq
    {A : Type} [CommRing A] [IsLocalRing A] {k : Type} [Field k]
    [Algebra k (ResidueField A)]
    (ρA : GaloisRepAdic A) (ρk : ResidualGaloisRep k)
    (e : ResidualGaloisRep.Equiv ρA.residual (ρk.baseChange (ResidueField A)))
    (bw : Module.Basis (Fin 2) k ρk.V) :
    ∃ β : Module.Basis (Fin 2) A ρA.V,
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j l : Fin 2),
        residue A (LinearMap.toMatrix β β (ρA.ρ σ) j l) =
          algebraMap k (ResidueField A) (LinearMap.toMatrix bw bw (ρk.ρ σ) j l) := by
  set k' := ResidueField A
  let b' : Module.Basis (Fin 2) k' (k' ⊗[k] ρk.V) := Algebra.TensorProduct.basis k' bw
  let b'' : Module.Basis (Fin 2) k' (k' ⊗[A] ρA.V) := b'.map e.toLinearEquiv.symm
  have hsurj : Function.Surjective (TensorProduct.mk A k' ρA.V 1) :=
    TensorProduct.mk_surjective A ρA.V k' residue_surjective
  choose v hv using fun j => hsurj (b'' j)
  have hcomp : (TensorProduct.mk A k' ρA.V 1) ∘ v = b'' := funext hv
  haveI : Module.FinitePresentation A ρA.V := Module.finitePresentation_of_projective A ρA.V
  obtain ⟨β, hβ⟩ := Module.exists_basis_of_basis_baseChange v
    (by rw [hcomp]; exact b''.linearIndependent) (by rw [hcomp]; exact b''.span_eq)
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hbasis : Algebra.TensorProduct.basis k' β = b'' := by
    refine Module.Basis.eq_of_apply_eq fun j => ?_
    rw [Algebra.TensorProduct.basis_apply, hβ, ← hv j]; rfl
  refine ⟨β, fun σ j l => ?_⟩
  have h1 : residue A (LinearMap.toMatrix β β (ρA.ρ σ) j l) =
      LinearMap.toMatrix b'' b'' ((ρA.ρ σ).baseChange k') j l := by
    rw [← hbasis, LinearMap.toMatrix_baseChange, Matrix.map_apply]; rfl
  rw [h1, LinearMap.toMatrix_apply]
  have h2 : ∀ x, b''.repr x = b'.repr (e.toLinearEquiv x) := fun x => by
    rw [Module.Basis.map_repr]; rfl
  have h3 : b'' l = e.toLinearEquiv.symm (b' l) := Module.Basis.map_apply _ _ _
  rw [h2, h3]
  have h4 : e.toLinearEquiv ((ρA.ρ σ).baseChange k' (e.toLinearEquiv.symm (b' l))) =
      (ρk.ρ σ).baseChange k' (b' l) := by
    have := e.map_apply σ (e.toLinearEquiv.symm (b' l))
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  rw [h4, ← LinearMap.toMatrix_apply, LinearMap.toMatrix_baseChange, Matrix.map_apply]

theorem repr_mem_of_mem_smul_top {A : Type} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]
    {ι : Type*} (b : Module.Basis ι A V) (I : Ideal A) {v : V}
    (hv : v ∈ I • (⊤ : Submodule A V)) (i : ι) : b.repr v i ∈ I := by
  refine Submodule.smul_induction_on hv (fun a ha w _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

theorem toMatrix_sub_one_mem {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
    {n : Type} [Fintype n] [DecidableEq n] (b : Module.Basis n A V) (I : Ideal A)
    (f : Module.End A V) (hf : ∀ v, f v - v ∈ I • (⊤ : Submodule A V)) (j l : n) :
    (LinearMap.toMatrix b b f - 1) j l ∈ I := by
  rw [← LinearMap.toMatrix_one b, ← map_sub, LinearMap.toMatrix_apply]
  exact repr_mem_of_mem_smul_top b I (hf (b l)) j

theorem mul_entry_mem_of_left {A : Type} [CommRing A] {n : Type} [Fintype n] {I : Ideal A}
    {X : Matrix n n A} (hX : ∀ j l, X j l ∈ I) (Y : Matrix n n A) (j l : n) : (X * Y) j l ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (hX j x)

theorem mul_entry_mem_of_right {A : Type} [CommRing A] {n : Type} [Fintype n] {I : Ideal A}
    (X : Matrix n n A) {Y : Matrix n n A} (hY : ∀ j l, Y j l ∈ I) (j l : n) : (X * Y) j l ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (hY x l)

theorem pi_mem_smul_top {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    {I : Ideal A} {x : n → A} (hx : ∀ j, x j ∈ I) : x ∈ I • (⊤ : Submodule A (n → A)) := by
  have : x = ∑ j, x j • (Pi.single j 1 : n → A) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hx j) Submodule.mem_top

end Models
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix"

section OfMatrix

variable {T : Type} [CommRing T] [IsLocalRing T]

noncomputable def ofMatrix (C : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) T)
    (hC : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ j l, (C σ - 1) j l ∈ maximalIdeal T ^ n) : GaloisRepAdic T where
  V := Fin 2 → T
  finrank_eq := Module.finrank_fin_fun T
  ρ := { toFun := fun σ => Matrix.toLin' (C σ)
         map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
         map_mul' := fun σ τ => by rw [map_mul, Matrix.toLin'_mul]; rfl }
  isAdicContinuous := by
    intro n
    obtain ⟨L, hL, h⟩ := hC n
    refine ⟨L, hL, fun σ hσ v => ?_⟩
    show Matrix.toLin' (C σ) v - v ∈ _
    rw [Matrix.toLin'_apply, show C σ *ᵥ v - v = (C σ - 1) *ᵥ v by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    exact pi_mem_smul_top fun j => by
      rw [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (h σ hσ j l)

theorem ofMatrix_baseChangeAlong_isEquiv
    (C : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) T)
    (hC : ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ j l, (C σ - 1) j l ∈ maximalIdeal T ^ n)
    {B : Type} [CommRing B] [IsLocalRing B] (φ : T →+* B) (hφ : IsLocalHom φ)
    (ρB : GaloisRepAdic B) (β : Module.Basis (Fin 2) B ρB.V) (P : Matrix (Fin 2) (Fin 2) B)
    (hP : IsUnit P)
    (hcomm : ∀ σ, LinearMap.toMatrix β β (ρB.ρ σ) * P = P * (C σ).map φ) :
    ((ofMatrix C hC).baseChangeAlong φ hφ).IsEquiv ρB := by
  letI : Algebra T B := φ.toAlgebra
  haveI hPinv : Invertible P := hP.invertible
  let e1 : B ⊗[T] (Fin 2 → T) ≃ₗ[B] (Fin 2 → B) := TensorProduct.piScalarRight T B B (Fin 2)
  let e2 : (Fin 2 → B) ≃ₗ[B] (Fin 2 → B) := Matrix.toLinearEquiv' P hPinv
  let e3 : (Fin 2 → B) ≃ₗ[B] ρB.V := β.equivFun.symm
  have he1 : ∀ (b : B) (f : Fin 2 → T), e1 (b ⊗ₜ f) = fun j => φ (f j) * b := fun b f => by
    show TensorProduct.piScalarRight T B B (Fin 2) (b ⊗ₜ f) = _
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    rfl
  have he1C : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (f : Fin 2 → T),
      e1 (b ⊗ₜ (C σ *ᵥ f)) = (C σ).map φ *ᵥ e1 (b ⊗ₜ f) := fun σ b f => by
    rw [he1, he1]
    funext j
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.map_apply, map_mul, mul_assoc]
  have he2 : ∀ u : Fin 2 → B, e2 u = P *ᵥ u := fun u => by
    show ((P.toLinearEquiv' hPinv : Module.End B (Fin 2 → B))) u = _
    rw [Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  have he3 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (u : Fin 2 → B),
      e3 (LinearMap.toMatrix β β (ρB.ρ σ) *ᵥ u) = ρB.ρ σ (e3 u) := fun σ u => by
    have h := LinearMap.toMatrix_mulVec_repr β β (ρB.ρ σ) (e3 u)
    have hu : ⇑(β.repr (e3 u)) = u := by
      show ⇑(β.repr (β.equivFun.symm u)) = u
      funext j
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hu] at h
    rw [h]
    show β.equivFun.symm ⇑(β.repr ((ρB.ρ σ) (e3 u))) = _
    rw [show (⇑(β.repr ((ρB.ρ σ) (e3 u))) : Fin 2 → B) = β.equivFun ((ρB.ρ σ) (e3 u)) from rfl,
      LinearEquiv.symm_apply_apply]
  have key : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : B ⊗[T] (Fin 2 → T)),
      (e1.trans (e2.trans e3)) ((Matrix.toLin' (C σ)).baseChange B y) =
        ρB.ρ σ ((e1.trans (e2.trans e3)) y) := by
    intro σ y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b f =>
      rw [LinearMap.baseChange_tmul, Matrix.toLin'_apply, LinearEquiv.trans_apply,
        LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply, he1C, he2, he2,
        Matrix.mulVec_mulVec, ← hcomm σ, ← Matrix.mulVec_mulVec, he3]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨{ toLinearEquiv := e1.trans (e2.trans e3), map_apply := fun σ x => key σ x }⟩

end OfMatrix
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix"

section Topology

variable (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]

theorem exists_maximalIdeal_pow_le_map (A : Type) [CommRing A] [IsLocalRing A] [Algebra T A]
    [Module.Finite T A] [IsLocalHom (algebraMap T A)] :
    ∃ c : ℕ, (maximalIdeal A) ^ c ≤ (maximalIdeal T).map (algebraMap T A) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing T A
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    haveI := hP
    have hcomap : (maximalIdeal T) ≤ P.comap (algebraMap T A) :=
      Ideal.le_comap_of_map_le hJP
    have hne : P.comap (algebraMap T A) ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    have heq : P.comap (algebraMap T A) = maximalIdeal T :=
      ((maximalIdeal.isMaximal T).eq_of_le hne hcomap).symm
    have hPmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (heq ▸ maximalIdeal.isMaximal T)
    rw [IsLocalRing.eq_maximalIdeal hPmax]
  · exact IsNoetherian.noetherian _

variable {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra T (A i)]

def diag : T →ₗ[T] (∀ i, A i) := LinearMap.pi fun i => Algebra.linearMap T (A i)

@[scoped simp] private theorem _root_.CarayolAsm.diag_apply (x : T) (i : Fin n) : diag T A x i = algebraMap T (A i) x := rfl

p2m_export "CarayolAsm" "diag_apply"

theorem mem_smul_top_pi (I : Ideal T) (z : ∀ i, A i)
    (hz : ∀ i, z i ∈ I.map (algebraMap T (A i))) :
    z ∈ I • (⊤ : Submodule T (∀ i, A i)) := by
  classical
  have hsingle : ∀ i, (Pi.single i (z i) : ∀ i, A i) ∈ I • (⊤ : Submodule T (∀ i, A i)) := by
    intro i
    have hzi : z i ∈ I • (⊤ : Submodule T (A i)) := by
      rw [Ideal.smul_top_eq_map]; exact hz i
    refine Submodule.smul_induction_on hzi (fun a ha w _ => ?_) (fun x y hx hy => ?_)
    · rw [Pi.single_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [Pi.single_add]
      exact Submodule.add_mem _ hx hy
  have : z = ∑ i, Pi.single i (z i) := by
    ext j
    simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => hsingle i

theorem exists_forall_mem_pow_of_forall [∀ i, IsLocalRing (A i)] [∀ i, Module.Finite T (A i)]
    [∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0) (M : ℕ) :
    ∃ N : ℕ, ∀ x : T, (∀ i, algebraMap T (A i) x ∈ maximalIdeal (A i) ^ N) →
      x ∈ maximalIdeal T ^ M := by
  choose c hc using fun i => exists_maximalIdeal_pow_le_map T (A i)
  obtain ⟨k0, hk0⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal T)
    (LinearMap.range (diag T A))
  refine ⟨(∑ i, c i) * (M + k0), fun x hx => ?_⟩

  have h1 : diag T A x ∈ maximalIdeal T ^ (M + k0) • (⊤ : Submodule T (∀ i, A i)) := by
    refine mem_smul_top_pi T A _ _ fun i => ?_
    rw [Ideal.map_pow, diag_apply]
    refine (Ideal.pow_right_mono (hc i) (M + k0)) ?_
    rw [← pow_mul]
    refine Ideal.pow_le_pow_right ?_ (hx i)
    exact Nat.mul_le_mul_right _ (Finset.single_le_sum (fun j _ => Nat.zero_le (c j))
      (Finset.mem_univ i))

  have h2 : diag T A x ∈ maximalIdeal T ^ (M + k0) • (⊤ : Submodule T (∀ i, A i)) ⊓
      LinearMap.range (diag T A) := ⟨h1, LinearMap.mem_range_self _ x⟩
  rw [hk0 (M + k0) (Nat.le_add_left k0 M), Nat.add_sub_cancel] at h2
  have h3 : diag T A x ∈ maximalIdeal T ^ M • LinearMap.range (diag T A) :=
    Submodule.smul_mono le_rfl inf_le_right h2
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h3
  obtain ⟨y, hy, hyx⟩ := h3
  have hinj' : Function.Injective (diag T A) := by
    intro a b hab
    rw [← sub_eq_zero]
    refine hinj _ fun i => ?_
    have := congrFun hab i
    rw [diag_apply, diag_apply] at this
    rw [map_sub, this, sub_self]
  rw [← hinj' hyx]
  rwa [smul_eq_mul, Ideal.mul_top] at hy

end Topology
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix"

theorem main
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → T)
    (htr : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      (ρ i).trace σ = algebraMap T (A i) (τ σ)) :
    ∃ ρ' : GaloisRepAdic T,
      ∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i)) := by
  classical

  let bw : Module.Basis (Fin 2) (ResidueField T) ρbar.V :=
    Module.finBasisOfFinrankEq (ResidueField T) ρbar.V ρbar.finrank_eq
  let Rbar := matrixHom bw ρbar.ρ
  have hspan : Submodule.span (ResidueField T) (Set.range ⇑Rbar) = ⊤ := by
    have h1 : Set.range ⇑Rbar =
        (LinearMap.toMatrix bw bw : Module.End (ResidueField T) ρbar.V →ₗ[ResidueField T]
          Matrix (Fin 2) (Fin 2) (ResidueField T)) '' Set.range ⇑ρbar.ρ := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, (ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top ρbar).mp
      habs, Submodule.map_top, LinearMap.range_eq_top]
    exact (LinearMap.toMatrix bw bw).surjective

  have hβ : ∀ i, ∃ β : Module.Basis (Fin 2) (A i) (ρ i).V,
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (j l : Fin 2),
        residue (A i) (LinearMap.toMatrix β β ((ρ i).ρ σ) j l) =
          ResidueField.map (algebraMap T (A i)) (Rbar σ j l) := by
    intro i
    letI : Algebra (ResidueField T) (ResidueField (A i)) :=
      (ResidueField.map (algebraMap T (A i))).toAlgebra
    exact exists_basis_residue_toMatrix_eq (ρ i) ρbar (Classical.choice (hres i)) bw
  choose β hβ using hβ

  let R : ∀ i, (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (A i) :=
    fun i => matrixHom (β i) (ρ i).ρ
  have hred : ∀ i g (j l : Fin 2),
      residue (A i) (R i g j l) = ResidueField.map (algebraMap T (A i)) (Rbar g j l) :=
    fun i g j l => hβ i g j l
  have htr' : ∀ i g, (R i g).trace = algebraMap T (A i) (τ g) := fun i g => by
    rw [← htr g i]
    show (LinearMap.toMatrix (β i) (β i) ((ρ i).ρ g)).trace = LinearMap.trace (A i) _ ((ρ i).ρ g)
    rw [LinearMap.trace_eq_matrix_trace (A i) (β i)]

  obtain ⟨C, P, -, hPu, hcomm⟩ :=
    CarayolMatrix.exists_monoidHom_matrix_forall_mul_eq_mul_map A hinj Rbar hspan R hred τ htr'

  have hC : ∀ M : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ j l, (C σ - 1) j l ∈ maximalIdeal T ^ M := by
    intro M
    obtain ⟨N, hN⟩ := exists_forall_mem_pow_of_forall T A hinj M
    choose L hLfin hL using fun i => (ρ i).isAdicContinuous N
    haveI := hLfin
    refine ⟨⨆ i, L i, IntermediateField.finiteDimensional_iSup_of_finite, fun σ hσ j l =>
      hN _ fun i => ?_⟩
    have hσi : ∀ x ∈ L i, σ x = x := fun x hx => hσ x (le_iSup L i hx)
    have h1 : ∀ j l, (R i σ - 1) j l ∈ maximalIdeal (A i) ^ N :=
      toMatrix_sub_one_mem (β i) _ ((ρ i).ρ σ) (hL i σ hσi)
    have hdet : IsUnit (P i).det := (Matrix.isUnit_iff_isUnit_det _).mp (hPu i)
    have h2 : (C σ - 1).map (algebraMap T (A i)) = (P i)⁻¹ * (R i σ - 1) * P i := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul _ hdet,
        Matrix.mul_assoc, hcomm i σ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 := mul_entry_mem_of_left (mul_entry_mem_of_right (P i)⁻¹ h1) (P i) j l
    rw [← h2, Matrix.map_apply] at h3
    exact h3
  exact ⟨ofMatrix C hC, fun i => ofMatrix_baseChangeAlong_isEquiv C hC (algebraMap T (A i)) (hloc i)
    (ρ i) (β i) (P i) (hPu i) fun σ => hcomm i σ⟩

end CarayolAsm
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix.Datum P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolMatrix P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq.CarayolAsm"

open IsLocalRing in
theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → T)
    (htr : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (i : Fin n),
      (ρ i).trace σ = algebraMap T (A i) (τ σ)) :
    ∃ ρ' : GaloisRepAdic T,
      ∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i)) :=
  CarayolAsm.main A hinj ρbar habs ρ hres τ htr

end S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq
end P2MW
export P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq (solution)
