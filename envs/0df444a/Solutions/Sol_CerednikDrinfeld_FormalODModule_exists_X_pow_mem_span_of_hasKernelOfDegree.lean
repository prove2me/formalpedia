-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1f7b5dbc-c9f3-5ce3-a67b-e50d26a9cab1

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace NilAux

open TensorProduct

section Coeff

variable {B : Type u} [CommRing B]

theorem exists_sum_smul_of_forall_coeff_mem {σ : Type*} (L : Ideal B) (hL : L.FG)
    (a : MvPowerSeries σ B) (ha : ∀ n, coeff n a ∈ L) :
    ∃ (k : ℕ) (g : Fin k → B) (h : Fin k → MvPowerSeries σ B), (∀ j, g j ∈ L) ∧ a = ∑ j, g j • h j := by
  classical
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  have hc : ∀ n, ∃ c : Fin k → B, ∑ j, c j * g j = coeff n a := by
    intro n
    have : coeff n a ∈ Ideal.span (Set.range g) := by
      show coeff n a ∈ Submodule.span B (Set.range g)
      rw [hg]; exact ha n
    exact Ideal.mem_span_range_iff_exists_fun.mp this
  choose c hc using hc
  refine ⟨k, g, fun j => fun n => c n j, fun j => ?_, ?_⟩
  · rw [← hg]; exact Submodule.subset_span ⟨j, rfl⟩
  · ext n
    rw [← hc n]
    simp only [map_sum, coeff_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl

theorem map_surjective_of_surjective {C : Type*} [CommRing C] (g : B →+* C) (hg : Function.Surjective g) :
    Function.Surjective (MvPowerSeries.map (σ := Fin 2) g) := by
  intro h
  refine ⟨fun d => (hg (coeff d h)).choose, ?_⟩
  ext d
  rw [coeff_map]
  exact (hg (coeff d h)).choose_spec

end Coeff

section Theta

variable {B : Type u} [CommRing B] (φ : Series B) (κ : Type u) [CommRing κ] [Algebra B κ]

noncomputable def theta :
    FormalODModule.KerAlgebra φ →+* FormalODModule.KerAlgebra (φ.map (algebraMap B κ)) :=
  Ideal.Quotient.lift (Ideal.span (Set.range φ))
    ((Ideal.Quotient.mk (Ideal.span (Set.range (φ.map (algebraMap B κ))))).comp
      (MvPowerSeries.map (algebraMap B κ)))
    (by
      have : Ideal.span (Set.range φ) ≤ RingHom.ker ((Ideal.Quotient.mk
          (Ideal.span (Set.range (φ.map (algebraMap B κ))))).comp (MvPowerSeries.map (algebraMap B κ))) := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨i, rfl⟩
      exact fun x hx => this hx)

theorem theta_mk (a : MvPowerSeries (Fin 2) B) :
    theta φ κ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap B κ) a) :=
  Ideal.Quotient.lift_mk _ _ _

theorem theta_surjective (hs : Function.Surjective (algebraMap B κ)) : Function.Surjective (theta φ κ) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _
    (Ideal.Quotient.mk_surjective.comp (map_surjective_of_surjective _ hs))

theorem theta_algebraMap (b : B) :
    theta φ κ (algebraMap B (FormalODModule.KerAlgebra φ) b) =
      algebraMap B (FormalODModule.KerAlgebra (φ.map (algebraMap B κ))) b := by
  rw [← Ideal.Quotient.mk_algebraMap, theta_mk, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, MvPowerSeries.map_C, IsScalarTower.algebraMap_apply B κ, ← Ideal.Quotient.mk_algebraMap,
    MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

noncomputable def thetaAlg :
    FormalODModule.KerAlgebra φ →ₐ[B] FormalODModule.KerAlgebra (φ.map (algebraMap B κ)) :=
  { toRingHom := theta φ κ, commutes' := theta_algebraMap φ κ }

noncomputable def Theta :
    κ ⊗[B] FormalODModule.KerAlgebra φ →ₗ[κ] FormalODModule.KerAlgebra (φ.map (algebraMap B κ)) :=
  LinearMap.liftBaseChange κ (thetaAlg φ κ).toLinearMap

theorem Theta_tmul (x : FormalODModule.KerAlgebra φ) : Theta φ κ ((1 : κ) ⊗ₜ[B] x) = theta φ κ x := by
  rw [Theta, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem Theta_surjective (hs : Function.Surjective (algebraMap B κ)) : Function.Surjective (Theta φ κ) := by
  intro y
  obtain ⟨x, rfl⟩ := theta_surjective φ κ hs y
  exact ⟨(1 : κ) ⊗ₜ x, Theta_tmul φ κ x⟩

theorem Theta_injective [IsNoetherianRing B] (hs : Function.Surjective (algebraMap B κ)) :
    Function.Injective (Theta φ κ) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  rw [LinearMap.mem_ker] at hz
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective B (FormalODModule.KerAlgebra φ) κ hs z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Theta φ κ ((1 : κ) ⊗ₜ[B] (Ideal.Quotient.mk _ a)) = 0 at hz
  rw [Theta_tmul, theta_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  have hI' : Ideal.span (Set.range (φ.map (algebraMap B κ))) =
      (Ideal.span (Set.range φ)).map (MvPowerSeries.map (algebraMap B κ)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hI', Ideal.mem_map_iff_of_surjective _ (map_surjective_of_surjective _ hs)] at hz
  obtain ⟨a', ha', haa'⟩ := hz
  have hcoeff : ∀ n, coeff n (a - a') ∈ RingHom.ker (algebraMap B κ) := by
    intro n
    have := congrArg (coeff n) haa'
    rw [coeff_map, coeff_map] at this
    rw [RingHom.mem_ker, map_sub, map_sub, sub_eq_zero]
    exact this.symm
  obtain ⟨k, g, h, hg, hsum⟩ :=
    exists_sum_smul_of_forall_coeff_mem _ (IsNoetherian.noetherian _) (a - a') hcoeff
  have ha : Ideal.Quotient.mk (Ideal.span (Set.range φ)) a =
      ∑ j, g j • Ideal.Quotient.mk (Ideal.span (Set.range φ)) (h j) := by
    have : Ideal.Quotient.mk (Ideal.span (Set.range φ)) a = Ideal.Quotient.mk _ (a - a') := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr ha', sub_zero]
    rw [this, hsum]
    show Ideal.Quotient.mkₐ B (Ideal.span (Set.range φ)) (∑ j, g j • h j) =
      ∑ j, g j • Ideal.Quotient.mkₐ B (Ideal.span (Set.range φ)) (h j)
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
  show (TensorProduct.mk B κ (FormalODModule.KerAlgebra φ) 1) (Ideal.Quotient.mk _ a) = 0
  rw [ha, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  show (1 : κ) ⊗ₜ[B] (g j • Ideal.Quotient.mk _ (h j)) = 0
  have h0 : g j • (1 : κ) = 0 := by
    have e : g j • (1 : κ) = algebraMap B κ (g j) * 1 := Algebra.smul_def (g j) (1 : κ)
    rw [e, mul_one]
    exact hg j
  rw [← TensorProduct.smul_tmul, h0, TensorProduct.zero_tmul]

end Theta

theorem finrank_fiber_kerAlgebra_eq_of_isMaximal {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) (p : PrimeSpectrum B) (hp : p.asIdeal.IsMaximal) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (FormalODModule.KerAlgebra φ)) = d := by
  classical
  haveI := hp
  have hs : Function.Surjective (algebraMap B p.asIdeal.ResidueField) :=
    Ideal.algebraMap_residueField_surjective p.asIdeal
  have hdimκ : Module.finrank p.asIdeal.ResidueField
      (FormalODModule.KerAlgebra (φ.map (algebraMap B p.asIdeal.ResidueField))) = d :=
    hφ.2.2 p.asIdeal.ResidueField (algebraMap B p.asIdeal.ResidueField)
  rw [← hdimκ]
  exact (LinearEquiv.ofBijective (Theta φ p.asIdeal.ResidueField)
    ⟨Theta_injective φ _ hs, Theta_surjective φ _ hs⟩).finrank_eq

theorem rankAtStalk_kerAlgebra_eq_of_isMaximal {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) (p : PrimeSpectrum B) (hp : p.asIdeal.IsMaximal) :
    Module.rankAtStalk (R := B) (FormalODModule.KerAlgebra φ) p = d := by
  haveI : Module.Finite B (FormalODModule.KerAlgebra φ) := hφ.1
  haveI : Module.Projective B (FormalODModule.KerAlgebra φ) := hφ.2.1
  rw [Module.rankAtStalk_eq]
  exact finrank_fiber_kerAlgebra_eq_of_isMaximal φ hφ p hp

theorem rankAtStalk_eq_of_forall_isMaximal {B : Type u} [CommRing B] {M : Type v} [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] {d : ℕ}
    (h : ∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal → Module.rankAtStalk M p = d) (p : PrimeSpectrum B) :
    Module.rankAtStalk M p = d := by
  haveI : Module.FinitePresentation B M := Module.finitePresentation_of_projective B M
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let q : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hq : Module.rankAtStalk M q = d := h q hm
  have hpq : p ≤ q := hle
  have hcl : q ∈ closure ({p} : Set (PrimeSpectrum B)) := (PrimeSpectrum.le_iff_mem_closure p q).mp hpq
  have hopen : IsOpen ((Module.rankAtStalk (R := B) M) ⁻¹' {d}) :=
    (Module.isLocallyConstant_rankAtStalk (R := B) (M := M)).isOpen_fiber d
  have hqU : q ∈ (Module.rankAtStalk (R := B) M) ⁻¹' {d} := hq
  obtain ⟨x, hxU, hxp⟩ := mem_closure_iff.mp hcl _ hopen hqU
  rw [Set.mem_singleton_iff] at hxp
  subst hxp
  exact hxU

theorem finrank_fiber_eq_of_forall_isMaximal {B : Type u} [CommRing B] {M : Type v} [AddCommGroup M] [Module B M]
    [Module.Finite B M] [Module.Projective B M] {d : ℕ}
    (h : ∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal → Module.rankAtStalk M p = d) (p : PrimeSpectrum B) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = d := by
  rw [← Module.rankAtStalk_eq, rankAtStalk_eq_of_forall_isMaximal h p]

theorem finrank_fiber_kerAlgebra_eq {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) (p : PrimeSpectrum B) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (FormalODModule.KerAlgebra φ)) = d := by
  haveI : Module.Finite B (FormalODModule.KerAlgebra φ) := hφ.1
  haveI : Module.Projective B (FormalODModule.KerAlgebra φ) := hφ.2.1
  exact finrank_fiber_eq_of_forall_isMaximal (fun q hq => rankAtStalk_kerAlgebra_eq_of_isMaximal φ hφ q hq) p

theorem rankAtStalk_kerAlgebra_eq {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) (p : PrimeSpectrum B) :
    Module.rankAtStalk (R := B) (FormalODModule.KerAlgebra φ) p = d := by
  haveI : Module.Finite B (FormalODModule.KerAlgebra φ) := hφ.1
  haveI : Module.Projective B (FormalODModule.KerAlgebra φ) := hφ.2.1
  exact rankAtStalk_eq_of_forall_isMaximal (fun q hq => rankAtStalk_kerAlgebra_eq_of_isMaximal φ hφ q hq) p

end NilAux

noncomputable section

open scoped Classical TensorProduct

namespace NilAug

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

section orderIdeals
variable {σ : Type*} {R : Type*} [CommRing R]

def J (σ : Type*) (R : Type*) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  add_mem' := by
    intro f g hf hg
    exact le_trans (le_min hf hg) min_order_le_add
  zero_mem' := by simp [order_zero]
  smul_mem' := by
    intro c f hf
    simp only [smul_eq_mul, Set.mem_setOf_eq]
    exact le_trans hf (le_trans le_add_self le_order_mul)

theorem mem_J {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ J σ R n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 := by
  constructor
  · intro hf d hd
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hd) hf
  · intro h
    exact nat_le_order h

theorem J_mul_le (a b : ℕ) : J σ R a * J σ R b ≤ J σ R (a + b) := by
  rw [Ideal.mul_le]
  intro f hf g hg
  show ((a + b : ℕ) : ℕ∞) ≤ (f * g).order
  push_cast
  exact le_trans (add_le_add hf hg) le_order_mul

theorem mem_J_one_iff {f : MvPowerSeries σ R} : f ∈ J σ R 1 ↔ constantCoeff f = 0 := by
  show ((1 : ℕ) : ℕ∞) ≤ f.order ↔ _
  rw [Nat.cast_one]
  exact one_le_order_iff_constCoeff_eq_zero

theorem J_one_ne_top [Nontrivial R] : J σ R 1 ≠ ⊤ := by
  intro h
  have : (1 : MvPowerSeries σ R) ∈ J σ R 1 := h ▸ Submodule.mem_top
  rw [mem_J_one_iff] at this
  simp at this

end orderIdeals

section two
variable {R : Type*} [CommRing R]

theorem degree_fin_two (β : Fin 2 →₀ ℕ) : β.degree = β 0 + β 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

def XI : Ideal (MvPowerSeries (Fin 2) R) := Ideal.span {X 0, X 1}

theorem XI_le_J_one : (XI : Ideal (MvPowerSeries (Fin 2) R)) ≤ J (Fin 2) R 1 := by
  rw [XI, Ideal.span_le]
  rintro f (rfl | rfl) <;> simp [SetLike.mem_coe, mem_J_one_iff]

theorem J_succ_le_XI_mul (n : ℕ) : J (Fin 2) R (n + 1) ≤ XI * J (Fin 2) R n := by
  intro f hf
  rw [mem_J] at hf
  let g₀ : MvPowerSeries (Fin 2) R := fun α => coeff (α + Finsupp.single 0 1) f
  let g₁ : MvPowerSeries (Fin 2) R := fun α => if α 0 = 0 then coeff (α + Finsupp.single 1 1) f else 0
  have hg₀ : g₀ ∈ J (Fin 2) R n := by
    rw [mem_J]; intro d hd
    show coeff (d + Finsupp.single 0 1) f = 0
    apply hf; simp [degree_fin_two] at hd ⊢; omega
  have hg₁ : g₁ ∈ J (Fin 2) R n := by
    rw [mem_J]; intro d hd
    show (if d 0 = 0 then coeff (d + Finsupp.single 1 1) f else 0) = 0
    split_ifs with h
    · apply hf; simp [degree_fin_two] at hd ⊢; omega
    · rfl
  have hdec : f = X 0 * g₀ + X 1 * g₁ := by
    ext d
    rw [map_add, X, X, coeff_monomial_mul, coeff_monomial_mul]
    by_cases h0 : d 0 = 0
    · by_cases h1 : d 1 = 0
      · have hd : d = 0 := by ext i; fin_cases i <;> simp [h0, h1]
        subst hd
        have := hf 0 (by simp)
        simp [this]
      · have hle : Finsupp.single (1 : Fin 2) 1 ≤ d := by
          intro i; fin_cases i <;> simp; omega
        have hnle : ¬ Finsupp.single (0 : Fin 2) 1 ≤ d := by
          intro h; have := h 0; simp at this; omega
        rw [if_neg hnle, if_pos hle, zero_add, one_mul]
        show coeff d f = if (d - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 then coeff (d - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0
        rw [if_pos (by simp [h0]), tsub_add_cancel_of_le hle]
    · have hle : Finsupp.single (0 : Fin 2) 1 ≤ d := by
        intro i; fin_cases i <;> simp; omega
      rw [if_pos hle, one_mul]
      have e1 : coeff (d - Finsupp.single 0 1) g₀ = coeff d f := by
        show coeff (d - Finsupp.single 0 1 + Finsupp.single 0 1) f = coeff d f
        rw [tsub_add_cancel_of_le hle]
      rw [e1]
      by_cases hle1 : Finsupp.single (1 : Fin 2) 1 ≤ d
      · rw [if_pos hle1, one_mul]
        have e2 : coeff (d - Finsupp.single 1 1) g₁ = 0 := by
          show (if (d - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 then coeff (d - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0) = 0
          rw [if_neg]; simp [h0]
        rw [e2, add_zero]
      · rw [if_neg hle1, add_zero]
  rw [hdec]
  exact Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hg₀)
    (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hg₁)

theorem J_le_XI_pow (n : ℕ) : J (Fin 2) R n ≤ XI ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    exact le_trans (J_succ_le_XI_mul n) (Ideal.mul_mono_right ih)

theorem sub_trunc_mem_J (f : MvPowerSeries (Fin 2) R) (r : ℕ) :
    f - ∑ α ∈ (Finset.range r ×ˢ Finset.range r).image
        (fun q : ℕ × ℕ => Finsupp.single (0 : Fin 2) q.1 + Finsupp.single 1 q.2),
        monomial α (coeff α f) ∈ J (Fin 2) R r := by
  rw [mem_J]
  intro d hd
  rw [map_sub, sub_eq_zero, map_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq]
  rw [if_pos]
  rw [Finset.mem_image]
  refine ⟨(d 0, d 1), ?_, by ext i; fin_cases i <;> simp⟩
  rw [degree_fin_two] at hd
  simp only [Finset.mem_product, Finset.mem_range]
  omega

end two

section fieldcase
variable {κ : Type*} [Field κ]

theorem exists_J_le_span {φ : Fin 2 → MvPowerSeries (Fin 2) κ} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite κ (MvPowerSeries (Fin 2) κ ⧸ Ideal.span (Set.range φ))) :
    ∃ r, J (Fin 2) κ r ≤ Ideal.span (Set.range φ) := by
  set I : Ideal (MvPowerSeries (Fin 2) κ) := Ideal.span (Set.range φ) with hIdef
  have hIJ : I ≤ J (Fin 2) κ 1 := by
    rw [hIdef, Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact mem_J_one_iff.mpr (hφ i)
  have hJtop : J (Fin 2) κ 1 ≠ ⊤ := J_one_ne_top
  have hItop : I ≠ ⊤ := fun h => hJtop (top_le_iff.mp (h ▸ hIJ))
  haveI : Nontrivial (MvPowerSeries (Fin 2) κ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (MvPowerSeries (Fin 2) κ ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (MvPowerSeries (Fin 2) κ ⧸ I) := IsArtinianRing.of_finite κ _
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := MvPowerSeries (Fin 2) κ ⧸ I)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hr
  have hmap : Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1) ≤ IsLocalRing.maximalIdeal _ := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : MvPowerSeries (Fin 2) κ ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1) :=
      htop ▸ Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨x, hx, hx1⟩ := h1
    have hx1' : x - 1 ∈ I := by rw [← Ideal.Quotient.eq, hx1, map_one]
    have : (1 : MvPowerSeries (Fin 2) κ) ∈ J (Fin 2) κ 1 := by
      have := (J (Fin 2) κ 1).sub_mem hx (hIJ hx1')
      rwa [sub_sub_cancel] at this
    exact hJtop (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  have hpow : Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1 ^ r) = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff]
    have := Ideal.pow_right_mono hmap r
    rw [hr] at this
    simpa using this
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow
  exact ⟨r, le_trans (J_le_XI_pow r) (le_trans (Ideal.pow_right_mono XI_le_J_one r) hpow)⟩

end fieldcase

end NilAug

namespace NilAug

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

section more
variable {σ : Type*} {R : Type*} [CommRing R]

theorem monomial_mem_J (d : σ →₀ ℕ) (a : R) : monomial d a ∈ J σ R d.degree := by
  rw [mem_J]
  intro e he
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact absurd he (lt_irrefl _)
  · rfl

theorem X_pow_mem_J (i : σ) (r : ℕ) : (X i : MvPowerSeries σ R) ^ r ∈ J σ R r := by
  have : (X i : MvPowerSeries σ R) ^ r = monomial (Finsupp.single i r) 1 := by
    rw [X_pow_eq]
  rw [this]
  have h := monomial_mem_J (R := R) (Finsupp.single i r) 1
  rwa [Finsupp.degree_single] at h

theorem exists_sum_smul_of_coeff_mem_span {s : ℕ} (m : Fin s → R) (u : MvPowerSeries σ R)
    (hu : ∀ d, coeff d u ∈ Ideal.span (Set.range m)) :
    ∃ w : Fin s → MvPowerSeries σ R, u = ∑ j, m j • w j := by
  have hc : ∀ d, ∃ c : Fin s → R, ∑ j, c j * m j = coeff d u := fun d =>
    Ideal.mem_span_range_iff_exists_fun.mp (hu d)
  choose c hc using hc
  refine ⟨fun j => fun d => c d j, ?_⟩
  ext d
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [← hc d]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_comm]
  rfl

end more

section fiber
variable {B : Type u} [CommRing B] (φ : Fin 2 → MvPowerSeries (Fin 2) B)
variable (C : Type u) [CommRing C] [Algebra B C]

abbrev bc : Fin 2 → MvPowerSeries (Fin 2) C := fun i => MvPowerSeries.map (algebraMap B C) (φ i)

abbrev KA : Type u := MvPowerSeries (Fin 2) B ⧸ Ideal.span (Set.range φ)
abbrev KAC : Type u := MvPowerSeries (Fin 2) C ⧸ Ideal.span (Set.range (bc φ C))

def θr : KA φ →+* KAC φ C :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPowerSeries.map (algebraMap B C))) (by
    intro a ha
    have : Ideal.span (Set.range φ) ≤ RingHom.ker ((Ideal.Quotient.mk (Ideal.span (Set.range (bc φ C)))).comp
        (MvPowerSeries.map (algebraMap B C))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap B C) (φ i)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    exact this ha)

theorem θr_mk (a : MvPowerSeries (Fin 2) B) :
    θr φ C (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap B C) a) := rfl

def θ : KA φ →ₐ[B] KAC φ C :=
  { θr φ C with
    commutes' := fun b => by
      show θr φ C (Ideal.Quotient.mk _ (algebraMap B (MvPowerSeries (Fin 2) B) b)) =
        Ideal.Quotient.mk _ (algebraMap B (MvPowerSeries (Fin 2) C) b)
      rw [θr_mk, MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, MvPowerSeries.map_C] }

theorem θ_mk (a : MvPowerSeries (Fin 2) B) :
    θ φ C (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (MvPowerSeries.map (algebraMap B C) a) := rfl

def Θ : C ⊗[B] KA φ →ₗ[C] KAC φ C := (θ φ C).toLinearMap.liftBaseChange C

theorem Θ_tmul (c : C) (m : KA φ) : Θ φ C (c ⊗ₜ m) = c • θ φ C m :=
  LinearMap.liftBaseChange_tmul _ _ _ _

end fiber

section fieldfiber
variable {B : Type u} [CommRing B] (φ : Fin 2 → MvPowerSeries (Fin 2) B)
variable (κ : Type u) [Field κ] [Algebra B κ]

theorem bc_constantCoeff {C : Type u} [CommRing C] [Algebra B C] (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (i : Fin 2) : constantCoeff (bc φ C i) = 0 := by
  show constantCoeff (MvPowerSeries.map _ (φ i)) = 0
  rw [constantCoeff_map, hφ0, map_zero]

theorem Θ_surjective (hφ0 : ∀ i, constantCoeff (φ i) = 0) (hfin : Module.Finite κ (KAC φ κ)) :
    Function.Surjective (Θ φ κ) := by
  obtain ⟨r, hr⟩ := exists_J_le_span (bc_constantCoeff φ hφ0) hfin
  rw [← LinearMap.range_eq_top, Θ, LinearMap.range_liftBaseChange, eq_top_iff]
  rintro y -
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hdec := sub_trunc_mem_J h r
  set T := ∑ α ∈ (Finset.range r ×ˢ Finset.range r).image
        (fun q : ℕ × ℕ => Finsupp.single (0 : Fin 2) q.1 + Finsupp.single 1 q.2),
        monomial α (coeff α h) with hT
  have : Ideal.Quotient.mk (Ideal.span (Set.range (bc φ κ))) h = Ideal.Quotient.mk _ T := by
    rw [Ideal.Quotient.eq]; exact hr hdec
  rw [this, hT, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have hθ : θ φ κ (Ideal.Quotient.mk _ (monomial α 1)) = Ideal.Quotient.mk _ (monomial α (1 : κ)) := by
    rw [θ_mk, MvPowerSeries.map_monomial, map_one]
  have e1 : monomial α (coeff α h) = coeff α h • (monomial α (1 : κ)) := by
    rw [← (monomial α).map_smul, smul_eq_mul, mul_one]
  have : (Ideal.Quotient.mk (Ideal.span (Set.range (bc φ κ)))) (monomial α (coeff α h)) =
      coeff α h • (Ideal.Quotient.mk (Ideal.span (Set.range (bc φ κ)))) (monomial α (1 : κ)) := by
    rw [e1]
    exact map_smul (Ideal.Quotient.mkₐ κ (Ideal.span (Set.range (bc φ κ)))) (coeff α h) (monomial α (1 : κ))
  rw [this, ← hθ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Ideal.Quotient.mk _ (monomial α 1), rfl⟩)

end fieldfiber

end NilAug

namespace NilAug

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

section main
variable {B : Type u} [CommRing B]

theorem nil_of_rank (φ : Fin 2 → MvPowerSeries (Fin 2) B) (hφ0 : ∀ i, constantCoeff (φ i) = 0) {d : ℕ}
    (hfinB : Module.Finite B (KA φ)) (hd : 0 < d)
    (h3 : ∀ (κ : Type u) [Field κ] [Algebra B κ], Module.finrank κ (KAC φ κ) = d)
    (hrank : ∀ p : PrimeSpectrum B, Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (KA φ)) = d) :
    ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) := by
  have key : ∀ i : Fin 2, IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range φ)) (X i : MvPowerSeries (Fin 2) B)) := by
    intro i
    rw [nilpotent_iff_mem_prime]
    intro 𝔮 h𝔮
    haveI := h𝔮
    haveI := hfinB
    let P : PrimeSpectrum B := ⟨𝔮.under B, inferInstance⟩
    let κ : Type u := P.asIdeal.ResidueField
    haveI hfinκ : Module.Finite κ (KAC φ κ) := Module.finite_of_finrank_pos (by rw [h3 κ]; exact hd)
    have hsurj := Θ_surjective φ κ hφ0 hfinκ
    have hinj : Function.Injective (Θ φ κ) := by
      rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      · exact hsurj
      · rw [h3 κ]; exact hrank P
    obtain ⟨r, hr⟩ := exists_J_le_span (bc_constantCoeff φ (C := κ) hφ0) hfinκ
    set x : KA φ := Ideal.Quotient.mk (Ideal.span (Set.range φ)) (X i) with hx
    have hzero : ((1 : κ) ⊗ₜ[B] (x ^ r) : P.asIdeal.Fiber (KA φ)) = 0 := by
      apply hinj
      rw [map_zero, Θ_tmul, one_smul, hx, ← map_pow, θ_mk, map_pow, MvPowerSeries.map_X]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hr (X_pow_mem_J i r))

    let L := 𝔮.ResidueField
    let Λ₀ : κ →ₐ[B] L := Ideal.ResidueField.mapₐ (𝔮.under B) 𝔮 (Algebra.ofId B (KA φ)) rfl
    let Λ : κ ⊗[B] KA φ →ₐ[B] L :=
      Algebra.TensorProduct.lift Λ₀ (IsScalarTower.toAlgHom B (KA φ) L) (fun _ _ => Commute.all _ _)
    have hΛ : Λ ((1 : κ) ⊗ₜ[B] (x ^ r)) = algebraMap (KA φ) L (x ^ r) := by
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    have : algebraMap (KA φ) L (x ^ r) = 0 := by rw [← hΛ, hzero, map_zero]
    rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] at this
    exact h𝔮.mem_of_pow_mem r this
  choose K hK using fun i => key i
  refine ⟨K 0 + K 1, fun i => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  apply pow_eq_zero_of_le ?_ (hK i)
  fin_cases i
  · exact Nat.le_add_right _ _
  · exact Nat.le_add_left _ _

end main

end NilAug

namespace NilAug

p2m_open "MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule"

section final
variable {B : Type u} [CommRing B]

theorem map_surjective_of_surjective {C : Type u} [CommRing C] (g : B →+* C) (hg : Function.Surjective g) :
    Function.Surjective (MvPowerSeries.map (σ := Fin 2) g) := by
  intro h
  refine ⟨fun d => (hg (coeff d h)).choose, ?_⟩
  ext d
  rw [coeff_map]
  exact (hg (coeff d h)).choose_spec

theorem θ_surjective_of_surjective (φ : Fin 2 → MvPowerSeries (Fin 2) B) (C : Type u) [CommRing C] [Algebra B C]
    (hg : Function.Surjective (algebraMap B C)) : Function.Surjective (θ φ C) := by
  intro y
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := map_surjective_of_surjective _ hg h
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem subsingleton_of_rank_zero (φ : Fin 2 → MvPowerSeries (Fin 2) B) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hfinB : Module.Finite B (KA φ))
    (h3 : ∀ (κ : Type u) [Field κ] [Algebra B κ], Module.finrank κ (KAC φ κ) = 0) : Subsingleton B := by
  by_contra hB
  rw [not_subsingleton_iff_nontrivial] at hB
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal B
  letI : Field (B ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI := hfinB
  haveI : Module.Finite B (KAC φ (B ⧸ 𝔪)) :=
    Module.Finite.of_surjective (θ φ (B ⧸ 𝔪)).toLinearMap
      (θ_surjective_of_surjective φ (B ⧸ 𝔪) Ideal.Quotient.mk_surjective)
  haveI : Module.Finite (B ⧸ 𝔪) (KAC φ (B ⧸ 𝔪)) := Module.Finite.of_restrictScalars_finite B (B ⧸ 𝔪) _
  have hsub : Subsingleton (KAC φ (B ⧸ 𝔪)) := Module.finrank_zero_iff.mp (h3 (B ⧸ 𝔪))
  have h1 : (1 : MvPowerSeries (Fin 2) (B ⧸ 𝔪)) ∈ Ideal.span (Set.range (bc φ (B ⧸ 𝔪))) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact Subsingleton.elim _ _
  have hle : Ideal.span (Set.range (bc φ (B ⧸ 𝔪))) ≤ J (Fin 2) (B ⧸ 𝔪) 1 := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact mem_J_one_iff.mpr (bc_constantCoeff φ hφ0 i)
  exact J_one_ne_top (Ideal.eq_top_of_isUnit_mem _ (hle h1) isUnit_one)

theorem nil (φ : Fin 2 → MvPowerSeries (Fin 2) B) (hφ0 : ∀ i, constantCoeff (φ i) = 0) {d : ℕ}
    (hφ : FormalODModule.HasKernelOfDegree φ d)
    (closed : ∀ p : PrimeSpectrum B, p.asIdeal.IsMaximal → Module.rankAtStalk (KA φ) p = d) :
    ∃ N : ℕ, ∀ i : Fin 2, (X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) := by
  have h3 : ∀ (κ : Type u) [Field κ] [Algebra B κ], Module.finrank κ (KAC φ κ) = d :=
    fun κ _ _ => hφ.2.2 κ (algebraMap B κ)
  by_cases hd : d = 0
  · subst hd
    haveI := subsingleton_of_rank_zero φ hφ0 hφ.1 h3
    refine ⟨0, fun i => ?_⟩
    rw [pow_zero]
    have : (1 : MvPowerSeries (Fin 2) B) = 0 := by
      ext d; exact Subsingleton.elim _ _
    rw [this]; exact Ideal.zero_mem _
  · haveI : Module.Finite B (KA φ) := hφ.1
    haveI : Module.Projective B (KA φ) := hφ.2.1
    have hrank := NilAux.finrank_fiber_eq_of_forall_isMaximal (M := KA φ) closed
    exact nil_of_rank φ hφ0 hφ.1 (Nat.pos_of_ne_zero hd) h3 hrank

end final

end NilAug

end

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (φ : Series B)
    (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) {d : ℕ} (hφ : FormalODModule.HasKernelOfDegree φ d) :
    ∃ N : ℕ, ∀ i : Fin 2, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ N ∈ Ideal.span (Set.range φ) :=
  NilAug.nil φ hφ0 hφ (fun p hp => NilAux.rankAtStalk_kerAlgebra_eq_of_isMaximal φ hφ p hp)

end S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_of_hasKernelOfDegree (solution)
