-- Prove2me | solution 1 for CohCarrier.exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1918d622-9cce-5f74-a312-bb73fa688288

import Mathlib
import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_IharaLemma_IdempotentSplitting
import Theorems.Thm_CohCarrier_heckeT_comm_of_prime
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace BridgeSol

open CohCarrier Polynomial IharaLemma

section Coeff

variable {𝒪 : Type} [CommRing 𝒪] {A B : Type} [AddCommGroup A] [AddCommGroup B]
  [Module 𝒪 A] [Module 𝒪 B] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def coefL (g : A →ₗ[𝒪] B) : H1 M H A →ₗ[𝒪] H1 M H B where
  toFun φ := g.toAddMonoidHom.comp φ
  map_add' φ ψ := by ext; simp
  map_smul' r φ := by ext; simp

@[scoped simp] theorem coefL_apply (g : A →ₗ[𝒪] B) (φ : H1 M H A) :
    coefL M H g φ = g.toAddMonoidHom.comp φ := rfl

end Coeff

section Corner

variable {𝒪 : Type} [CommRing 𝒪]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable (Sp : IdempotentSplitting 𝕋) (i₀ : Fin Sp.n)

theorem exists_mul_mul_e_eq {u : 𝕋} (hu : u ∉ Sp.𝔪 i₀) : ∃ t : 𝕋, t * u * Sp.e i₀ = Sp.e i₀ :=
  exists_mul_mul_eq_of_notMem (Sp.idem i₀) (Sp.𝔪 i₀) (Sp.mem_of_isMaximal_of_ne i₀) hu

theorem e_smul_eq_of_mem {v : V} (hv : v ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    Sp.e i₀ • v = v :=
  Sp.e_smul_coe i₀ ⟨v, hv⟩

theorem smul_mem_corner (t : 𝕋) {v : V} (hv : v ∈ cornerSubmodule (M := V) (Sp.e i₀)) :
    t • v ∈ cornerSubmodule (M := V) (Sp.e i₀) :=
  Submodule.smul_mem _ t hv

theorem e_smul_mem_corner (v : V) : Sp.e i₀ • v ∈ cornerSubmodule (M := V) (Sp.e i₀) :=
  ⟨v, rfl⟩

theorem exists_eq_smul_of_smul_eq_smul {s : 𝕋} (hs : s ∉ Sp.𝔪 i₀) (ϖ : 𝒪) {v y : V}
    (hv : v ∈ cornerSubmodule (M := V) (Sp.e i₀)) (h : s • v = ϖ • y) :
    ∃ v₁ : V, v₁ ∈ cornerSubmodule (M := V) (Sp.e i₀) ∧ v = ϖ • v₁ := by
  obtain ⟨t, ht⟩ := exists_mul_mul_e_eq Sp i₀ hs
  refine ⟨t • Sp.e i₀ • y, smul_mem_corner Sp i₀ t (e_smul_mem_corner Sp i₀ y), ?_⟩
  have hem : Sp.e i₀ • v = v := e_smul_eq_of_mem Sp i₀ hv
  calc v = (t * s * Sp.e i₀) • v := by rw [ht, hem]
    _ = t • (s • (Sp.e i₀ • v)) := by rw [smul_smul, smul_smul]
    _ = t • (Sp.e i₀ • (s • v)) := by rw [smul_comm s (Sp.e i₀) v]
    _ = t • (Sp.e i₀ • (ϖ • y)) := by rw [h]
    _ = ϖ • t • Sp.e i₀ • y := by rw [smul_comm (Sp.e i₀) ϖ y, smul_comm t ϖ]

end Corner

section Sep

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {ι : Type} (T : ι → Module.End k V) (θ : ι → k)

theorem aeval_mem_of_forall_mem (f : Module.End k V) (W : Submodule k V)
    (hW : ∀ w ∈ W, f w ∈ W) (p : k[X]) : ∀ w ∈ W, aeval f p w ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro w hw
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem (hp w hw) (hq w hw)
  | monomial n a =>
    intro w hw
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, Module.End.mul_apply,
      Module.algebraMap_end_apply]
    refine W.smul_mem a ?_
    induction n generalizing w with
    | zero => simpa using hw
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply]
      exact ih (f w) (hW w hw)

theorem sub_smul_one_pow_mem_of_forall_mem (f : Module.End k V) (μ : k) (W : Submodule k V)
    (hW : ∀ w ∈ W, f w ∈ W) (n : ℕ) : ∀ w ∈ W, ((f - μ • (1 : Module.End k V)) ^ n) w ∈ W := by
  intro w hw
  have : (f - μ • (1 : Module.End k V)) ^ n = aeval f ((X - C μ) ^ n) := by
    rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact aeval_mem_of_forall_mem f W hW _ w hw

variable (hcomm : ∀ i j, Commute (T i) (T j))
include hcomm

theorem mem_maxGenEigenspace_of_mem (i j : ι) (v : V)
    (hv : v ∈ (T i).maxGenEigenspace (θ i)) : T j v ∈ (T i).maxGenEigenspace (θ i) := by
  rw [Module.End.mem_maxGenEigenspace] at hv ⊢
  obtain ⟨n, hn⟩ := hv
  refine ⟨n, ?_⟩
  have hc : Commute ((T i - θ i • (1 : Module.End k V)) ^ n) (T j) :=
    (((hcomm i j).sub_left ((Commute.one_left (T j)).smul_left (θ i))).pow_left n)
  have := congrArg (fun g : Module.End k V => g v) hc.eq
  simp only [Module.End.mul_apply] at this
  rw [this, hn, map_zero]

theorem mem_ker_of_mem (i j : ι) (v : V)
    (hv : v ∈ LinearMap.ker (T i - θ i • (1 : Module.End k V))) :
    T j v ∈ LinearMap.ker (T i - θ i • (1 : Module.End k V)) := by
  rw [LinearMap.mem_ker] at hv ⊢
  have hc : Commute (T i - θ i • (1 : Module.End k V)) (T j) :=
    (hcomm i j).sub_left ((Commute.one_left (T j)).smul_left (θ i))
  have := congrArg (fun g : Module.End k V => g v) hc.eq
  simp only [Module.End.mul_apply] at this
  rw [this, hv, map_zero]

variable (hnew : ∀ v : V, (∀ i, T i v = θ i • v) → v = 0)
include hnew

theorem eq_bot_of_forall_le_maxGenEigenspace (n : ℕ) :
    ∀ W : Submodule k V, Module.finrank k W ≤ n → (∀ i, ∀ w ∈ W, T i w ∈ W) →
      (∀ i, W ≤ (T i).maxGenEigenspace (θ i)) → W = ⊥ := by
  induction n with
  | zero =>
    intro W hW _ _
    exact Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
  | succ n ih =>
    intro W hW hst hle
    by_contra hne
    by_cases hall : ∀ i, W ≤ LinearMap.ker (T i - θ i • (1 : Module.End k V))
    · obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      apply hw0
      apply hnew w
      intro i
      have := hall i hwW
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero] at this
      exact this
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      set f : Module.End k V := T i - θ i • (1 : Module.End k V) with hf
      set W' : Submodule k V := W ⊓ LinearMap.ker f with hW'
      have hlt : W' < W := lt_of_le_of_ne inf_le_left (fun h => hi (h ▸ inf_le_right))
      have hrank : Module.finrank k W' ≤ n :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hW)
      have hst' : ∀ j, ∀ w ∈ W', T j w ∈ W' := fun j w hw =>
        ⟨hst j w hw.1, mem_ker_of_mem T θ hcomm i j w hw.2⟩
      have hle' : ∀ j, W' ≤ (T j).maxGenEigenspace (θ j) := fun j => le_trans inf_le_left (hle j)
      have hbot : W' = ⊥ := ih W' hrank hst' hle'
      obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hex : ∃ m : ℕ, (f ^ m) w = 0 := by
        have := hle i hwW
        rw [Module.End.mem_maxGenEigenspace] at this
        exact this
      classical
      have hm₀ : (f ^ Nat.find hex) w = 0 := Nat.find_spec hex
      have hm₀pos : Nat.find hex ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hm₀
        exact hw0 hm₀
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm₀pos
      have hwm : (f ^ m) w ≠ 0 := Nat.find_min hex (by rw [hm]; exact Nat.lt_succ_self m)
      have hmem : (f ^ m) w ∈ W' := by
        refine ⟨sub_smul_one_pow_mem_of_forall_mem (T i) (θ i) W (hst i) m w hwW, ?_⟩
        show (f ^ m) w ∈ LinearMap.ker f
        rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
        rw [hm] at hm₀
        exact hm₀
      rw [hbot, Submodule.mem_bot] at hmem
      exact hwm hmem

theorem exists_list_forall_mem_prod_apply_eq_zero (n : ℕ) :
    ∀ W : Submodule k V, Module.finrank k W ≤ n → (∀ i, ∀ w ∈ W, T i w ∈ W) →
      ∃ L : List (ι × k[X]), (∀ p ∈ L, (p.2).eval (θ p.1) ≠ 0) ∧
        ∀ w ∈ W, (L.map fun p => aeval (T p.1) p.2).prod w = 0 := by
  induction n with
  | zero =>
    intro W hW _
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    refine ⟨[], by simp, fun w hw => ?_⟩
    rw [hbot, Submodule.mem_bot] at hw
    rw [hw, map_zero]
  | succ n ih =>
    intro W hW hst
    by_cases hall : ∀ i, W ≤ (T i).maxGenEigenspace (θ i)
    · have hbot : W = ⊥ :=
        eq_bot_of_forall_le_maxGenEigenspace T θ hcomm hnew (n + 1) W hW hst hall
      refine ⟨[], by simp, fun w hw => ?_⟩
      rw [hbot, Submodule.mem_bot] at hw
      rw [hw, map_zero]
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      set K : Submodule k V := (T i).maxGenEigenspace (θ i) with hK
      have hχ : (T i).charpoly ≠ 0 := (LinearMap.charpoly_monic (T i)).ne_zero
      obtain ⟨g, hg, hndvd⟩ :=
        Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd _ hχ (θ i)
      have hgθ : g.eval (θ i) ≠ 0 := fun h => hndvd (Polynomial.dvd_iff_isRoot.mpr h)
      have hrange : ∀ v : V, aeval (T i) g v ∈ K := by
        intro v
        rw [hK, Module.End.mem_maxGenEigenspace]
        refine ⟨(T i).charpoly.rootMultiplicity (θ i), ?_⟩
        have h0 : aeval (T i) (T i).charpoly = 0 := LinearMap.aeval_self_charpoly (T i)
        rw [hg, map_mul, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h0
        have := congrArg (fun F : Module.End k V => F v) h0
        simpa only [Module.End.mul_apply, LinearMap.zero_apply] using this
      set W' : Submodule k V := W ⊓ K with hW'
      have hlt : W' < W := lt_of_le_of_ne inf_le_left (fun h => hi (h ▸ inf_le_right))
      have hrank : Module.finrank k W' ≤ n :=
        Nat.lt_succ_iff.mp (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hW)
      have hst' : ∀ j, ∀ w ∈ W', T j w ∈ W' := fun j w hw =>
        ⟨hst j w hw.1, mem_maxGenEigenspace_of_mem T θ hcomm i j w hw.2⟩
      obtain ⟨L', hL'good, hL'kill⟩ := ih W' hrank hst'
      refine ⟨L' ++ [(i, g)], ?_, ?_⟩
      · intro p hp
        rw [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hL'good p hp
        · exact hgθ
      · intro w hw
        rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
          Module.End.mul_apply]
        exact hL'kill _ ⟨aeval_mem_of_forall_mem (T i) W (hst i) g w hw, hrange w⟩

theorem exists_list_prod_aeval_eq_zero :
    ∃ L : List (ι × k[X]), (∀ p ∈ L, (p.2).eval (θ p.1) ≠ 0) ∧
      (L.map fun p => aeval (T p.1) p.2).prod = 0 := by
  obtain ⟨L, hgood, hkill⟩ := exists_list_forall_mem_prod_apply_eq_zero T θ hcomm hnew
    (Module.finrank k V) ⊤ (by rw [finrank_top]) (fun _ _ _ => Submodule.mem_top)
  exact ⟨L, hgood, LinearMap.ext fun v => hkill v Submodule.mem_top⟩

end Sep

section Plumbing

variable {R : Type} [CommRing R]

theorem aeval_smul_eq {𝕋 : Type} [CommRing 𝕋] [Algebra R 𝕋] {V : Type} [AddCommGroup V]
    [Module R V] [Module 𝕋 V] [IsScalarTower R 𝕋 V] (t : 𝕋) (T : Module.End R V)
    (h : ∀ v, t • v = T v) (p : R[X]) : ∀ v, (aeval t p) • v = aeval T p v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro v; rw [map_add, map_add, add_smul, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro v
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, aeval_C,
      aeval_X, mul_smul, algebraMap_smul, Module.End.mul_apply, Module.algebraMap_end_apply]
    congr 1
    induction n generalizing v with
    | zero => rw [pow_zero, pow_zero, one_smul, Module.End.one_apply]
    | succ n ih => rw [pow_succ, mul_smul, h, ih, pow_succ, Module.End.mul_apply]

theorem listProd_smul_eq {𝕋 : Type} [CommRing 𝕋] [Algebra R 𝕋] {V : Type} [AddCommGroup V]
    [Module R V] [Module 𝕋 V] [IsScalarTower R 𝕋 V] {ι : Type} (t : ι → 𝕋)
    (T : ι → Module.End R V) (L : List (ι × R[X]))
    (h : ∀ p ∈ L, ∀ v, t p.1 • v = T p.1 v) :
    ∀ v, (L.map fun p => aeval (t p.1) p.2).prod • v = (L.map fun p => aeval (T p.1) p.2).prod v := by
  induction L with
  | nil => intro v; simp
  | cons a L ih =>
    intro v
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mul_smul,
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp)), Module.End.mul_apply,
      aeval_smul_eq (t a.1) (T a.1) (h a List.mem_cons_self) a.2]

theorem apply_aeval_eq {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (S : Module.End R V) (T : Module.End R W) (h : ∀ v, f (S v) = T (f v))
    (p : R[X]) : ∀ v, f (aeval S p v) = aeval T p (f v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro v; rw [map_add, map_add, LinearMap.add_apply, map_add, hp, hq,
      LinearMap.add_apply]
  | monomial n a =>
    intro v
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, aeval_C,
      aeval_X, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
    congr 1
    induction n generalizing v with
    | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Module.End.mul_apply]

theorem apply_listProd_eq {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) {ι : Type} (S : ι → Module.End R V) (T : ι → Module.End R W)
    (L : List (ι × R[X])) (h : ∀ p ∈ L, ∀ v, f (S p.1 v) = T p.1 (f v)) :
    ∀ v, f ((L.map fun p => aeval (S p.1) p.2).prod v) =
      (L.map fun p => aeval (T p.1) p.2).prod (f v) := by
  induction L with
  | nil => intro v; simp
  | cons a L ih =>
    intro v
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, apply_aeval_eq f (S a.1) (T a.1) (h a List.mem_cons_self) a.2,
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

theorem aeval_apply_eq_aeval_map_apply {k : Type} [CommRing k] [Algebra R k] {V : Type}
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]
    (TR : Module.End R V) (Tk : Module.End k V) (h : ∀ v, TR v = Tk v) (p : R[X]) :
    ∀ v, aeval TR p v = aeval Tk (p.map (algebraMap R k)) v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro v; rw [map_add, Polynomial.map_add, map_add, LinearMap.add_apply,
      LinearMap.add_apply, hp, hq]
  | monomial n a =>
    intro v
    rw [← C_mul_X_pow_eq_monomial, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow, aeval_C, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, algebraMap_smul]
    congr 1
    induction n generalizing v with
    | zero => rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Module.End.mul_apply]

theorem listProd_apply_eq_listProd_map_apply {k : Type} [CommRing k] [Algebra R k] {V : Type}
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V] {ι : Type}
    (TR : ι → Module.End R V) (Tk : ι → Module.End k V) (h : ∀ i v, TR i v = Tk i v)
    (L : List (ι × R[X])) :
    ∀ v, (L.map fun p => aeval (TR p.1) p.2).prod v =
      (L.map fun p => aeval (Tk p.1) ((p.2).map (algebraMap R k))).prod v := by
  induction L with
  | nil => intro v; simp
  | cons a L ih =>
    intro v
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, ih, aeval_apply_eq_aeval_map_apply (TR a.1) (Tk a.1) (h a.1) a.2]

theorem mvAeval_listProd {ι S : Type} [CommRing S] [Algebra R S] (x : ι → S) (L : List (ι × R[X])) :
    MvPolynomial.aeval x (L.map fun p => aeval (MvPolynomial.X p.1 : MvPolynomial ι R) p.2).prod =
      (L.map fun p => aeval (x p.1) p.2).prod := by
  rw [map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp_apply]
  rw [← aeval_algHom_apply, MvPolynomial.aeval_X]

end Plumbing

section Main

abbrev kk (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] : Type := IsLocalRing.ResidueField 𝒪

abbrev gg (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] : 𝒪 →ₗ[𝒪] kk 𝒪 :=
  Algebra.linearMap 𝒪 (kk 𝒪)

theorem exists_eq_smul_of_forall_apply {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {ϖ : 𝒪}
    (hϖ0 : ϖ ≠ 0) {M : ℕ} {H : Subgroup (ZMod M)ˣ} (z : H1 M H 𝒪)
    (hz : ∀ γ, ∃ a, z γ = ϖ * a) : ∃ y : H1 M H 𝒪, z = ϖ • y := by
  choose f hf using hz
  refine ⟨{ toFun := f, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · apply mul_left_cancel₀ hϖ0
    rw [← hf, map_zero, mul_zero]
  · intro a b
    apply mul_left_cancel₀ hϖ0
    rw [mul_add, ← hf, ← hf, ← hf, map_add]
  · ext γ
    exact hf γ

open scoped IsMulCommutative in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem main
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (M : ℕ) [NeZero M] (S : Set ℕ)
    (hcomm : ∀ g g' : CohCarrier.Gen M S,
      CohCarrier.opFamily M ⊤ S 𝒪 g * CohCarrier.opFamily M ⊤ S 𝒪 g' =
        CohCarrier.opFamily M ⊤ S 𝒪 g' * CohCarrier.opFamily M ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen M S → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)
    {ι : Type} (ℓ : ι → ℕ) (hℓ : ∀ i : ι, (ℓ i).Prime) (hℓS : ∀ i : ι, ℓ i ∉ S)
    (hℓM : ∀ i : ι, ¬ ℓ i ∣ M) (c : ι → IsLocalRing.ResidueField 𝒪)
    (hnew : ∀ v : CohCarrier.H1 M ⊤ (IsLocalRing.ResidueField 𝒪),
      (∀ i : ι, (haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩;
        CohCarrier.heckeT M ⊤ (ℓ i) (IsLocalRing.ResidueField 𝒪) v) = c i • v) →
      v = 0)
    (i₀ : Fin Sp.n) :
    ∃ f : MvPolynomial ι 𝒪,
      MvPolynomial.aeval (R := 𝒪) c f = 0 ∧
      MvPolynomial.aeval (R := 𝒪)
          (fun i : ι => (⟨(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op
              (CohCarrier.Gen.T (ℓ i) (hℓ i) (hℓS i) (hℓM i)),
            Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
            ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)) f
        ∉ Sp.𝔪 i₀ := by
  classical

  set 𝕋sub := (CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra
    with h𝕋sub
  let tT : ι → ↥𝕋sub := fun i =>
    ⟨(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op
      (CohCarrier.Gen.T (ℓ i) (hℓ i) (hℓS i) (hℓM i)), Algebra.subset_adjoin (Set.mem_range_self _)⟩
  show ∃ f : MvPolynomial ι 𝒪, MvPolynomial.aeval (R := 𝒪) c f = 0 ∧
    MvPolynomial.aeval (R := 𝒪) tT f ∉ Sp.𝔪 i₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪

  have hg : ∀ a : 𝒪, gg 𝒪 a = IsLocalRing.residue 𝒪 a := fun a => rfl
  have hker : ∀ a, gg 𝒪 a = 0 → ∃ a₁, a = ϖ * a₁ := by
    intro a ha
    rw [hg, IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
    obtain ⟨a₁, rfl⟩ := ha
    exact ⟨a₁, by rw [mul_comm]⟩
  have hsurj : Function.Surjective (algebraMap 𝒪 (kk 𝒪)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective

  let Tk : ι → Module.End (kk 𝒪) (H1 M ⊤ (kk 𝒪)) := fun i =>
    haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩
    heckeTLin (kk 𝒪) (kk 𝒪) M ⊤ (ℓ i)
  have hTk : ∀ (i : ι) (v : H1 M ⊤ (kk 𝒪)),
      Tk i v = @heckeT M ⊤ (ℓ i) (kk 𝒪) _ ⟨(hℓ i).ne_zero⟩ v := fun i v => rfl
  have hcommk : ∀ i j : ι, Commute (Tk i) (Tk j) := by
    intro i j
    by_cases hij : ℓ i = ℓ j
    ·
      have key : ∀ (a b : ℕ) (hab : a = b) (h₁ : NeZero a) (h₂ : NeZero b) (w : H1 M ⊤ (kk 𝒪)),
          @heckeT M ⊤ a (kk 𝒪) _ h₁ w = @heckeT M ⊤ b (kk 𝒪) _ h₂ w := by
        intro a b hab
        subst hab
        intro h₁ h₂ w
        rfl
      have hTij : Tk i = Tk j := LinearMap.ext fun w => by
        rw [hTk, hTk]
        exact key _ _ hij _ _ w
      rw [hTij]
    · haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩
      haveI : NeZero (ℓ j) := ⟨(hℓ j).ne_zero⟩
      have hcop : Nat.Coprime (ℓ i) (ℓ j) := (Nat.coprime_primes (hℓ i) (hℓ j)).mpr hij
      refine LinearMap.ext fun v => ?_
      exact heckeT_comm_of_prime M ⊤ (ℓ i) (ℓ j) (hℓ i) hcop v
  have hnew' : ∀ v : H1 M ⊤ (kk 𝒪), (∀ i : ι, Tk i v = c i • v) → v = 0 := fun v hv =>
    hnew v (fun i => hv i)
  haveI : Module.Finite (kk 𝒪) (H1 M ⊤ (kk 𝒪)) := CohCarrier.H1_moduleFinite M ⊤ (kk 𝒪) (kk 𝒪)
  obtain ⟨L₀, hL₀good, hL₀kill⟩ := exists_list_prod_aeval_eq_zero Tk c hcommk hnew'

  let lift : (kk 𝒪)[X] → 𝒪[X] := fun g => (Polynomial.map_surjective _ hsurj g).choose
  have hlift : ∀ g : (kk 𝒪)[X], (lift g).map (algebraMap 𝒪 (kk 𝒪)) = g := fun g =>
    (Polynomial.map_surjective _ hsurj g).choose_spec
  let Lt : List (ι × 𝒪[X]) := L₀.map fun p => (p.1, lift p.2)

  let TA : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A], ι → Module.End 𝒪 (H1 M ⊤ A) :=
    fun A _ _ i =>
      haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩
      heckeTLin 𝒪 A M ⊤ (ℓ i)
  have hTA : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A] (i : ι) (v : H1 M ⊤ A),
      TA A i v = @heckeT M ⊤ (ℓ i) A _ ⟨(hℓ i).ne_zero⟩ v := fun A _ _ i v => rfl
  let Φ : ∀ (A : Type) [AddCommGroup A] [Module 𝒪 A], Module.End 𝒪 (H1 M ⊤ A) :=
    fun A _ _ => (Lt.map fun p => aeval (TA A p.1) p.2).prod
  let P : MvPolynomial ι 𝒪 := (Lt.map fun p => aeval (MvPolynomial.X p.1 : MvPolynomial ι 𝒪) p.2).prod
  let tn : ↥𝕋sub := (Lt.map fun p => aeval (tT p.1) p.2).prod
  have hPtn : MvPolynomial.aeval (R := 𝒪) tT P = tn := mvAeval_listProd tT Lt

  have hF1 : ∀ v : H1 M ⊤ 𝒪, tn • v = Φ 𝒪 v := by
    refine listProd_smul_eq tT (TA 𝒪) Lt ?_
    intro p _ v
    rw [hTA]
    rfl

  have hF2 : ∀ v : H1 M ⊤ 𝒪, coefL M ⊤ (gg 𝒪) (Φ 𝒪 v) = Φ (kk 𝒪) (coefL M ⊤ (gg 𝒪) v) := by
    refine apply_listProd_eq (coefL M ⊤ (gg 𝒪)) (TA 𝒪) (TA (kk 𝒪)) Lt ?_
    intro p _ v
    haveI : NeZero (ℓ p.1) := ⟨(hℓ p.1).ne_zero⟩
    rw [hTA, hTA, coefL_apply, coefL_apply]
    exact (heckeT_comp_coeff M ⊤ (ℓ p.1) (gg 𝒪).toAddMonoidHom v).symm

  have hF3 : ∀ w : H1 M ⊤ (kk 𝒪), Φ (kk 𝒪) w = 0 := by
    intro w
    have e1 := listProd_apply_eq_listProd_map_apply (TA (kk 𝒪)) Tk (fun i v => rfl) Lt w
    rw [e1]
    have e2 : (Lt.map fun p => aeval (Tk p.1) ((p.2).map (algebraMap 𝒪 (kk 𝒪)))) =
        (L₀.map fun p => aeval (Tk p.1) p.2) := by
      simp only [Lt, List.map_map]
      refine List.map_congr_left fun p _ => ?_
      simp only [Function.comp_apply, hlift]
    rw [e2, hL₀kill, LinearMap.zero_apply]

  have hdivV : ∀ v : H1 M ⊤ 𝒪, ∃ y : H1 M ⊤ 𝒪, tn • v = ϖ • y := by
    intro v
    have hz : coefL M ⊤ (gg 𝒪) (tn • v) = 0 := by
      rw [hF1, hF2, hF3]
    refine exists_eq_smul_of_forall_apply hϖ.ne_zero (tn • v) fun γ => hker _ ?_
    have := congrArg (fun F : H1 M ⊤ (kk 𝒪) => F γ) hz
    exact this

  have htn : tn ∈ Sp.𝔪 i₀ := by
    by_contra hnot

    let Y : Submodule 𝒪 (H1 M ⊤ 𝒪) :=
      (cornerSubmodule (M := H1 M ⊤ 𝒪) (Sp.e i₀)).restrictScalars 𝒪
    have hYdiv : Y ≤ IsLocalRing.maximalIdeal 𝒪 • Y := by
      intro v hv
      obtain ⟨y, hy⟩ := hdivV v
      obtain ⟨v₁, hv₁, rfl⟩ := exists_eq_smul_of_smul_eq_smul Sp i₀ hnot ϖ hv hy
      refine Submodule.smul_mem_smul ?_ hv₁
      rw [hϖ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self ϖ
    haveI : Module.Finite 𝒪 (H1 M ⊤ 𝒪) := CohCarrier.H1_moduleFinite M ⊤ 𝒪 𝒪
    haveI : IsNoetherian 𝒪 (H1 M ⊤ 𝒪) := isNoetherian_of_isNoetherianRing_of_finite 𝒪 _
    have hYfg : Y.FG := IsNoetherian.noetherian Y
    have hYbot : Y = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ Y hYfg hYdiv
        (IsLocalRing.maximalIdeal_le_jacobson _)

    have he0 : Sp.e i₀ = 0 := by
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      have hmem : Sp.e i₀ • v ∈ Y := e_smul_mem_corner Sp i₀ v
      rw [hYbot, Submodule.mem_bot] at hmem
      exact hmem
    exact Sp.notMem i₀ (he0 ▸ Submodule.zero_mem _)

  let abar : kk 𝒪 := (L₀.map fun p => (p.2).eval (c p.1)).prod
  have habar : abar ≠ 0 := by
    apply List.prod_ne_zero
    intro h0
    obtain ⟨p, hp, hp0⟩ := List.mem_map.mp h0
    exact hL₀good p hp hp0
  obtain ⟨a, ha⟩ := hsurj abar
  have haunit : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hmem
    apply habar
    rw [← ha, IsLocalRing.ResidueField.algebraMap_eq]
    exact (IsLocalRing.residue_eq_zero_iff a).mpr hmem
  have hPc : MvPolynomial.aeval (R := 𝒪) c P = abar := by
    rw [mvAeval_listProd c Lt]
    simp only [abar, Lt, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
    simp only [Function.comp_apply]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hlift]

  refine ⟨P - MvPolynomial.C a, ?_, ?_⟩
  · rw [map_sub, hPc, MvPolynomial.aeval_C, ha, sub_self]
  · rw [map_sub, hPtn, MvPolynomial.aeval_C]
    intro hmem
    have hamem : algebraMap 𝒪 (↥𝕋sub) a ∈ Sp.𝔪 i₀ := by
      have := (Sp.𝔪 i₀).sub_mem htn hmem
      rwa [sub_sub_cancel] at this
    exact (Sp.isMaximal i₀).ne_top (Ideal.eq_top_of_isUnit_mem _ hamem (haunit.map _))

end Main

end BridgeSol
p2m_reactivate "P2MW.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero.BridgeSol"

open scoped IsMulCommutative in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (M : ℕ) [NeZero M] (S : Set ℕ)
    (hcomm : ∀ g g' : CohCarrier.Gen M S,
      CohCarrier.opFamily M ⊤ S 𝒪 g * CohCarrier.opFamily M ⊤ S 𝒪 g' =
        CohCarrier.opFamily M ⊤ S 𝒪 g' * CohCarrier.opFamily M ⊤ S 𝒪 g)
    (θbar : CohCarrier.Gen M S → IsLocalRing.ResidueField 𝒪)
    (Sp : IharaLemma.IdempotentSplitting
      ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)

    {ι : Type} (ℓ : ι → ℕ) (hℓ : ∀ i : ι, (ℓ i).Prime) (hℓS : ∀ i : ι, ℓ i ∉ S)
    (hℓM : ∀ i : ι, ¬ ℓ i ∣ M) (c : ι → IsLocalRing.ResidueField 𝒪)
    (hnew : ∀ v : CohCarrier.H1 M ⊤ (IsLocalRing.ResidueField 𝒪),
      (∀ i : ι, (haveI : NeZero (ℓ i) := ⟨(hℓ i).ne_zero⟩;
        CohCarrier.heckeT M ⊤ (ℓ i) (IsLocalRing.ResidueField 𝒪) v) = c i • v) →
      v = 0)
    (i₀ : Fin Sp.n) :
    ∃ f : MvPolynomial ι 𝒪,
      MvPolynomial.aeval (R := 𝒪) c f = 0 ∧
      MvPolynomial.aeval (R := 𝒪)
          (fun i : ι => (⟨(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).op
              (CohCarrier.Gen.T (ℓ i) (hℓ i) (hℓS i) (hℓM i)),
            Algebra.subset_adjoin (Set.mem_range_self _)⟩ :
            ↥(CohCarrier.hdata M ⊤ S 𝒪 (IsLocalRing.ResidueField 𝒪) hcomm θbar).opSubalgebra)) f
        ∉ Sp.𝔪 i₀ :=
  BridgeSol.main M S hcomm θbar Sp ℓ hℓ hℓS hℓM c hnew i₀

end
p2m_reactivate "P2MW.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero.BridgeSol"

end S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero
end P2MW
export P2MW.S_CohCarrier_exists_mvPolynomial_aeval_eq_zero_and_aeval_notMem_of_forall_eq_zero (solution)
