-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.chartERing.infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/24364644-dcd5-5695-a3e9-381edc160b9d

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace DimOne29

open MvPolynomial

theorem ringKrullDim_le_of_isLocalization {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    (Monotone.strictMono_of_injective (fun _ _ h => Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective S M))

section

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ)

noncomputable abbrev πQ : edgeQuot 𝒪 π := algebraMap 𝒪 (edgeQuot 𝒪 π) π

abbrev Q₁ : Type := edgeQuot 𝒪 π ⧸ Ideal.span {πQ 𝒪 π}

noncomputable def ψ : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) →+* Q₁ 𝒪 π :=
  MvPolynomial.eval₂Hom
    (Ideal.quotientMap (Ideal.span {πQ 𝒪 π}) (algebraMap 𝒪 (edgeQuot 𝒪 π))
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.subset_span rfl))))
    (fun i => Ideal.Quotient.mk _ (edgeQuot.mk 𝒪 π (MvPolynomial.X i)))

theorem ψ_comp_map :
    (ψ 𝒪 π).comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪)))) =
      (Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π})).comp (edgeQuot.mk 𝒪 π).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    show ψ 𝒪 π (MvPolynomial.map _ (MvPolynomial.C a)) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.C a))
    rw [MvPolynomial.map_C, ψ, MvPolynomial.eval₂Hom_C, Ideal.quotientMap_mk, ← MvPolynomial.algebraMap_eq,
      AlgHom.commutes]
  · intro i
    show ψ 𝒪 π (MvPolynomial.map _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X i))
    rw [MvPolynomial.map_X, ψ, MvPolynomial.eval₂Hom_X']

theorem ψ_surjective : Function.Surjective (ψ 𝒪 π) := by
  have h : Function.Surjective ((ψ 𝒪 π).comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪))))) := by
    rw [ψ_comp_map]
    exact Ideal.Quotient.mk_surjective.comp (Ideal.Quotient.mkₐ_surjective 𝒪 _)
  exact Function.Surjective.of_comp h

theorem ψ_X (i : Fin 2) :
    ψ 𝒪 π (MvPolynomial.X i) = Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X i)) := by
  rw [ψ, MvPolynomial.eval₂Hom_X']

theorem ψ_X_mul_X : ψ 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1) = 0 := by
  have hrel : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) 𝒪) = edgeRel 𝒪 π + MvPolynomial.C π :=
    (sub_add_cancel _ _).symm
  have h1 : ψ 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1) =
      Ideal.Quotient.mk (Ideal.span {πQ 𝒪 π}) (edgeQuot.mk 𝒪 π (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
    rw [map_mul, ψ_X, ψ_X, map_mul, map_mul]
  rw [h1, hrel, map_add, edgeQuot.mk_edgeRel, zero_add, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

theorem ringKrullDim_Q₁_le (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) : ringKrullDim (Q₁ 𝒪 π) ≤ 1 := by
  letI : Field (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Ideal.Quotient.field _
  have hnzd : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪))) ∈
      nonZeroDivisors _ :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
  have h := ringKrullDim_succ_le_of_surjective (ψ 𝒪 π) (ψ_surjective 𝒪 π) hnzd (ψ_X_mul_X 𝒪 π)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
  have h2 : (0 : WithBot ℕ∞) + (Nat.card (Fin 2) : ℕ) = 1 + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  rw [h2] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

abbrev T : Type :=
  MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) ⧸
    Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)))}

noncomputable def χ₀ : MvPolynomial (Fin 2) 𝒪 →+* T 𝒪 π :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪))))

theorem χ₀_C_π : χ₀ 𝒪 π (MvPolynomial.C π) = 0 := by
  simp only [χ₀, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl : π ∈ Ideal.span ({π} : Set 𝒪)),
    MvPolynomial.C_0, map_zero]

theorem χ₀_edgeRel : χ₀ 𝒪 π (edgeRel 𝒪 π) = 0 := by
  rw [edgeRel, map_sub, χ₀_C_π, sub_zero]
  simp only [χ₀, RingHom.coe_comp, Function.comp_apply, map_mul, MvPolynomial.map_X]
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

noncomputable def χQ : edgeQuot 𝒪 π →+* T 𝒪 π :=
  show (MvPolynomial (Fin 2) 𝒪 ⧸ Ideal.span {edgeRel 𝒪 π}) →+* T 𝒪 π from
    Ideal.Quotient.lift _ (χ₀ 𝒪 π) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, χ₀_edgeRel, mul_zero])

theorem χQ_mk (f : MvPolynomial (Fin 2) 𝒪) : χQ 𝒪 π (edgeQuot.mk 𝒪 π f) = χ₀ 𝒪 π f :=
  Ideal.Quotient.lift_mk _ _ _

noncomputable def χ : Q₁ 𝒪 π →+* T 𝒪 π :=
  Ideal.Quotient.lift _ (χQ 𝒪 π) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, πQ, ← AlgHom.commutes (edgeQuot.mk 𝒪 π), MvPolynomial.algebraMap_eq, χQ_mk, χ₀_C_π,
      mul_zero])

theorem χ_comp_ψ : (χ 𝒪 π).comp (ψ 𝒪 π) = Ideal.Quotient.mk _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show χ 𝒪 π (ψ 𝒪 π (MvPolynomial.C (Ideal.Quotient.mk _ a))) = _
    rw [ψ, MvPolynomial.eval₂Hom_C, Ideal.quotientMap_mk, χ, Ideal.Quotient.lift_mk,
      ← AlgHom.commutes (edgeQuot.mk 𝒪 π), MvPolynomial.algebraMap_eq, χQ_mk]
    simp only [χ₀, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C]
  · intro i
    show χ 𝒪 π (ψ 𝒪 π (MvPolynomial.X i)) = _
    rw [ψ_X, χ, Ideal.Quotient.lift_mk, χQ_mk]
    simp only [χ₀, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X]

theorem ker_ψ_le : RingHom.ker (ψ 𝒪 π) ≤
    Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)))} := by
  intro f hf
  rw [RingHom.mem_ker] at hf
  have : Ideal.Quotient.mk _ f = (0 : T 𝒪 π) := by
    rw [← χ_comp_ψ]; simp only [RingHom.coe_comp, Function.comp_apply, hf, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

theorem isRadical_span_X_mul_X (k : Type) [Field k] :
    (Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) k)}).IsRadical := by
  intro f hf
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hf
  rw [Ideal.mem_span_singleton] at hn ⊢
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∣ f :=
    (MvPolynomial.X_prime (i := 0)).dvd_of_dvd_pow ((dvd_mul_right _ _).trans hn)
  have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∣ f :=
    (MvPolynomial.X_prime (i := 1)).dvd_of_dvd_pow ((dvd_mul_left _ _).trans hn)
  obtain ⟨g, rfl⟩ := h0
  rcases (MvPolynomial.X_prime (i := 1)).dvd_or_dvd h1 with h | h
  · exact absurd (MvPolynomial.X_dvd_X.mp h) (by decide)
  · exact mul_dvd_mul_left _ h

theorem ker_ψ : RingHom.ker (ψ 𝒪 π) =
      Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)))} :=
  le_antisymm (ker_ψ_le 𝒪 π) ((Ideal.span_singleton_le_iff_mem _).mpr (ψ_X_mul_X 𝒪 π))

theorem isReduced_Q₁ (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal) : IsReduced (Q₁ 𝒪 π) := by
  letI : Field (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Ideal.Quotient.field _
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective (ψ_surjective 𝒪 π)]
  have hker : RingHom.ker (ψ 𝒪 π) =
      Ideal.span {(MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)))} :=
    le_antisymm (ker_ψ_le 𝒪 π) ((Ideal.span_singleton_le_iff_mem _).mpr (ψ_X_mul_X 𝒪 π))
  rw [hker]
  exact isRadical_span_X_mul_X _

end

end DimOne29

namespace Inf29

open Polynomial

theorem infinite_setOf_isMaximal_not_mem (k : Type) [Field k] (h : k[X]) (hh : h ≠ 0) :
    Set.Infinite {m : Ideal k[X] | m.IsMaximal ∧ h ∉ m} := by
  intro hfin

  have hne : ∀ m ∈ hfin.toFinset, ∃ g : k[X], g ∈ m ∧ g ≠ 0 := by
    intro m hm
    have hm' := (hfin.mem_toFinset.mp hm).1
    have hbot : m ≠ ⊥ := fun hb => by
      rw [hb] at hm'
      have htop : Ideal.span ({X} : Set k[X]) = ⊤ :=
        hm'.out.2 _ (bot_lt_iff_ne_bot.mpr (by simpa using (Polynomial.X_ne_zero : (X : k[X]) ≠ 0)))
      exact Polynomial.not_isUnit_X (Ideal.span_singleton_eq_top.mp htop)
    obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨g, hg, hg0⟩
  choose g hg using hne
  set a : k[X] := ∏ m ∈ hfin.toFinset.attach, g m.1 m.2 with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Finset.prod_ne_zero_iff]
    intro m _
    exact (hg m.1 m.2).2
  have hamem : ∀ m (hm : m ∈ hfin.toFinset), a ∈ m := by
    intro m hm
    rw [ha, ← Finset.prod_erase_mul _ _ (Finset.mem_attach _ ⟨m, hm⟩)]
    exact Ideal.mul_mem_left _ _ (hg m hm).1

  set f : k[X] := X * (a * h) + 1 with hf
  have hfu : ¬ IsUnit f := by
    intro hu
    obtain ⟨u, -, hu'⟩ := Polynomial.isUnit_iff.mp hu
    have hdeg := congrArg (fun q : k[X] => q.coeff ((a * h).natDegree + 1)) hu'
    simp only [hf, coeff_add, coeff_X_mul, coeff_one, coeff_C, Nat.succ_ne_zero, if_false, add_zero] at hdeg
    exact (mul_ne_zero ha0 hh) (leadingCoeff_eq_zero.mp hdeg.symm)
  obtain ⟨m₀, hm₀, hfm₀⟩ := Ideal.exists_le_maximal (Ideal.span {f}) (Ideal.span_singleton_ne_top hfu)
  have hfm : f ∈ m₀ := hfm₀ (Ideal.subset_span rfl)
  have key : X * (a * h) ∉ m₀ := by
    intro hx
    have : (1 : k[X]) ∈ m₀ := by
      have := m₀.sub_mem hfm hx
      rwa [hf, add_sub_cancel_left] at this
    exact hm₀.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hhm₀ : h ∉ m₀ := fun hx => key (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hx))
  have hm₀S : m₀ ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hm₀, hhm₀⟩
  exact key (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hamem m₀ hm₀S)))

end Inf29

namespace Inf29

open MvPolynomial

variable (k : Type) [CommRing k]

noncomputable def φ (i : Fin 2) : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun l => if l = i then 0 else Polynomial.X)

theorem φ_X_self (i : Fin 2) : φ k i (MvPolynomial.X i) = 0 := by
  rw [φ, MvPolynomial.eval₂Hom_X']; simp

theorem φ_X_of_ne {i j : Fin 2} (h : j ≠ i) : φ k i (MvPolynomial.X j) = Polynomial.X := by
  rw [φ, MvPolynomial.eval₂Hom_X']; simp [h]

theorem φ_C (i : Fin 2) (a : k) : φ k i (MvPolynomial.C a) = Polynomial.C a := by
  rw [φ, MvPolynomial.eval₂Hom_C]

theorem φ_surjective (i : Fin 2) : Function.Surjective (φ k i) := by
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
  have hcomp : (φ k i).comp (Polynomial.eval₂RingHom (MvPolynomial.C) (MvPolynomial.X j)) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a; simp [Polynomial.eval₂RingHom, φ_C]
    · simp [Polynomial.eval₂RingHom, φ_X_of_ne k hj]
  intro g
  exact ⟨Polynomial.eval₂RingHom (MvPolynomial.C) (MvPolynomial.X j) g, by
    have := congrArg (fun f => f g) hcomp; simpa using this⟩

theorem φ_discr_ne_zero [IsDomain k] (i : Fin 2) (r : ℕ) (hr : 2 ≤ r) :
    φ k i ((MvPolynomial.X 0 ^ (r - 1) - 1) * (MvPolynomial.X 1 ^ (r - 1) - 1)) ≠ 0 := by
  have hr' : r - 1 ≠ 0 := by omega
  have hX : (Polynomial.X : Polynomial k) ^ (r - 1) - 1 ≠ 0 := by
    rw [← Polynomial.C_1]; exact (Polynomial.monic_X_pow_sub_C (1 : k) hr').ne_zero
  have h0 : (0 : Polynomial k) ^ (r - 1) - 1 ≠ 0 := by
    rw [zero_pow hr', zero_sub]; exact neg_ne_zero.mpr one_ne_zero
  have key : ∀ j : Fin 2, φ k i (MvPolynomial.X j) ^ (r - 1) - 1 ≠ 0 := by
    intro j
    by_cases hji : j = i
    · subst hji; rw [φ_X_self]; exact h0
    · rw [φ_X_of_ne k hji]; exact hX
  rw [map_mul, map_sub, map_sub, map_pow, map_pow, map_one]
  exact mul_ne_zero (key 0) (key 1)

end Inf29

open DimOne29

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (r : ℕ) (hπ : (Ideal.span ({π} : Set 𝒪)).IsMaximal)
    (p : Ideal ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) (hp : p ∈ minimalPrimes ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))) :
    Set.Infinite {q : PrimeSpectrum ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) | p ≤ q.asIdeal} := by
  classical
  letI instField : Field (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) := Ideal.Quotient.field _
  have hpP : p.IsPrime := hp.1.1

  rcases Nat.lt_or_ge r 2 with hr | hr
  · exfalso
    have hd0 : edgeQuot.discr 𝒪 π r = 0 := by
      show edgeQuot.mk 𝒪 π (edgeDiscr 𝒪 r) = 0
      have : r - 1 = 0 := by omega
      simp [edgeDiscr, this]
    haveI : Subsingleton (chartERing 𝒪 π r) :=
      (IsLocalization.uniqueOfZeroMem (M := Submonoid.powers (edgeQuot.discr 𝒪 π r))
        (S := chartERing 𝒪 π r) (by rw [hd0]; exact Submonoid.mem_powers _)).instSubsingleton
    haveI : Subsingleton ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) :=
      Ideal.Quotient.mk_surjective.subsingleton
    have h10 : (1 : (chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) = 0 :=
      Subsingleton.elim _ _
    exact hpP.ne_top ((Ideal.eq_top_iff_one p).mpr (h10.symm ▸ p.zero_mem))

  have hI : Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)} =
      (Ideal.span {πQ 𝒪 π}).map (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r)) := by
    rw [zero_add, pow_one, Ideal.map_span, Set.image_singleton, πQ, ← IsScalarTower.algebraMap_apply]
  set M₁ : Submonoid (Q₁ 𝒪 π) :=
    Algebra.algebraMapSubmonoid (Q₁ 𝒪 π) (Submonoid.powers (edgeQuot.discr 𝒪 π r)) with hM₁
  let e := Ideal.quotEquivOfEq hI
  letI instAlg : Algebra (Q₁ 𝒪 π) ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) :=
    (e.symm.toRingHom.comp (algebraMap (Q₁ 𝒪 π) _)).toAlgebra
  let e' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {πQ 𝒪 π}).map (algebraMap (edgeQuot 𝒪 π) (chartERing 𝒪 π r))) ≃ₐ[Q₁ 𝒪 π]
      ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) :=
    AlgEquiv.ofRingEquiv (f := e.symm) (fun _ => rfl)
  haveI instLoc : IsLocalization M₁ ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) :=
    IsLocalization.isLocalization_of_algEquiv M₁ e'

  set alg := algebraMap (Q₁ 𝒪 π) ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)}))
    with halg

  set d₁ : Q₁ 𝒪 π := algebraMap (edgeQuot 𝒪 π) (Q₁ 𝒪 π) (edgeQuot.discr 𝒪 π r) with hd₁
  set dk : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)) :=
    (MvPolynomial.X 0 ^ (r - 1) - 1) * (MvPolynomial.X 1 ^ (r - 1) - 1) with hdk
  have hψd : ψ 𝒪 π dk = d₁ := by
    have h1 : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span ({π} : Set 𝒪))) (edgeDiscr 𝒪 r) = dk := by
      simp [edgeDiscr, hdk, map_mul, map_sub, map_pow, MvPolynomial.map_X, map_one]
    have h2 := congrArg (fun f => f (edgeDiscr 𝒪 r)) (ψ_comp_map 𝒪 π)
    simp only [RingHom.coe_comp, Function.comp_apply, h1] at h2
    exact h2
  have hM₁mem : ∀ x ∈ M₁, ∃ n : ℕ, x = d₁ ^ n := by
    rintro x ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by rw [map_pow]⟩
  have hd₁M : d₁ ∈ M₁ := ⟨edgeQuot.discr 𝒪 π r, Submonoid.mem_powers _, rfl⟩
  have hdisj_of : ∀ q : Ideal (Q₁ 𝒪 π), q.IsPrime → d₁ ∉ q → Disjoint (M₁ : Set (Q₁ 𝒪 π)) q := by
    intro q hq hd
    refine Set.disjoint_left.mpr fun x hx hxq => ?_
    obtain ⟨n, rfl⟩ := hM₁mem x hx
    exact hd (hq.mem_of_pow_mem n hxq)

  set p₁ : Ideal (Q₁ 𝒪 π) := p.comap alg with hp₁def
  obtain ⟨hp₁', hdisj'⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint M₁ _ p).mp hpP
  haveI hp₁ : p₁.IsPrime := hp₁'
  have hdisj : Disjoint (M₁ : Set (Q₁ 𝒪 π)) (p₁ : Set (Q₁ 𝒪 π)) := hdisj'
  have hmc : p₁.map alg = p := IsLocalization.map_comap M₁ _ p
  have hp₁min : ∀ q : Ideal (Q₁ 𝒪 π), q.IsPrime → q ≤ p₁ → p₁ ≤ q := by
    intro q hq hle
    have hdq : Disjoint (M₁ : Set (Q₁ 𝒪 π)) (q : Set (Q₁ 𝒪 π)) :=
      Set.disjoint_left.mpr fun x hx hxq => Set.disjoint_left.mp hdisj hx (hle hxq)
    have hq' : (q.map alg).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M₁ _ q hq hdq
    have hle' : q.map alg ≤ p := by rw [← hmc]; exact Ideal.map_mono hle
    have hpq : p ≤ q.map alg := hp.2 ⟨hq', bot_le⟩ hle'
    calc p₁ ≤ (q.map alg).comap alg := Ideal.comap_mono hpq
      _ = q := IsLocalization.comap_map_of_isPrime_disjoint M₁ _ hq hdq
  have hd₁p₁ : d₁ ∉ p₁ := fun h => Set.disjoint_left.mp hdisj hd₁M h

  have hψsurj := ψ_surjective 𝒪 π
  have hXY : MvPolynomial.X 0 * MvPolynomial.X 1 ∈ p₁.comap (ψ 𝒪 π) := by
    rw [Ideal.mem_comap, ψ_X_mul_X]; exact Ideal.zero_mem _

  have main : ∀ i : Fin 2, MvPolynomial.X i ∣ (MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪))) → MvPolynomial.X i ∈ p₁.comap (ψ 𝒪 π) →
      Set.Infinite {q : PrimeSpectrum ((chartERing 𝒪 π r) ⧸
        (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (0 + 1)})) | p ≤ q.asIdeal} := by
    intro i hdvd hi
    have hkerle : RingHom.ker (ψ 𝒪 π) ≤ Ideal.span {MvPolynomial.X i} := by
      rw [ker_ψ]; exact Ideal.span_singleton_le_span_singleton.mpr hdvd
    haveI hXp : (Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin 2) (𝒪 ⧸ Ideal.span ({π} : Set 𝒪)))}).IsPrime :=
      (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero i)).mpr MvPolynomial.X_prime
    have hprime₀ : ((Ideal.span {MvPolynomial.X i}).map (ψ 𝒪 π)).IsPrime :=
      Ideal.map_isPrime_of_surjective hψsurj hkerle
    have hle₀ : (Ideal.span {MvPolynomial.X i}).map (ψ 𝒪 π) ≤ p₁ := by
      rw [← Ideal.map_comap_of_surjective (ψ 𝒪 π) hψsurj p₁]
      exact Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr hi)
    have hp₁eq : p₁ = (Ideal.span {MvPolynomial.X i}).map (ψ 𝒪 π) :=
      le_antisymm (hp₁min _ hprime₀ hle₀) hle₀

    have hh : Inf29.φ _ i dk ≠ 0 := Inf29.φ_discr_ne_zero _ i r hr
    have hS := Inf29.infinite_setOf_isMaximal_not_mem _ _ hh
    haveI := hS.to_subtype

    have hfam : ∀ m : {m : Ideal (Polynomial (𝒪 ⧸ Ideal.span ({π} : Set 𝒪))) | m.IsMaximal ∧ Inf29.φ _ i dk ∉ m},
        (((m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).map alg).IsPrime ∧
        p ≤ ((m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).map alg ∧
        (((m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).map alg).comap alg = (m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π) ∧
        ((m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).comap (ψ 𝒪 π) = m.1.comap (Inf29.φ _ i) := by
      rintro ⟨m, hm, hhm⟩
      have f1 : Ideal.span {MvPolynomial.X i} ≤ m.comap (Inf29.φ _ i) := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, Inf29.φ_X_self]; exact Ideal.zero_mem _
      have f2 : RingHom.ker (ψ 𝒪 π) ≤ m.comap (Inf29.φ _ i) := hkerle.trans f1
      haveI : (m.comap (Inf29.φ _ i)).IsPrime := Ideal.comap_isPrime _ _
      have f3 : ((m.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).IsPrime := Ideal.map_isPrime_of_surjective hψsurj f2
      have f7 : ((m.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).comap (ψ 𝒪 π) = m.comap (Inf29.φ _ i) := by
        rw [Ideal.comap_map_of_surjective _ hψsurj]; exact sup_eq_left.mpr f2
      have f4 : d₁ ∉ (m.comap (Inf29.φ _ i)).map (ψ 𝒪 π) := by
        intro hmem
        have : dk ∈ ((m.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).comap (ψ 𝒪 π) := by
          rw [Ideal.mem_comap, hψd]; exact hmem
        rw [f7, Ideal.mem_comap] at this
        exact hhm this
      have hdq := hdisj_of _ f3 f4
      refine ⟨IsLocalization.isPrime_of_isPrime_disjoint M₁ _ _ f3 hdq, ?_,
        IsLocalization.comap_map_of_isPrime_disjoint M₁ _ f3 hdq, f7⟩
      rw [← hmc, hp₁eq]
      exact Ideal.map_mono (Ideal.map_mono f1)
    refine Set.infinite_of_injective_forall_mem
      (f := fun m : {m : Ideal (Polynomial (𝒪 ⧸ Ideal.span ({π} : Set 𝒪))) | m.IsMaximal ∧ Inf29.φ _ i dk ∉ m} =>
        (⟨((m.1.comap (Inf29.φ _ i)).map (ψ 𝒪 π)).map alg, (hfam m).1⟩ : PrimeSpectrum _)) ?_ (fun m => (hfam m).2.1)
    intro m m' hmm'
    have h1 := congrArg (fun q : PrimeSpectrum _ => (q.asIdeal.comap alg).comap (ψ 𝒪 π)) hmm'
    simp only at h1
    rw [(hfam m).2.2.1, (hfam m').2.2.1, (hfam m).2.2.2, (hfam m').2.2.2] at h1
    have h2 := congrArg (Ideal.map (Inf29.φ _ i)) h1
    rw [Ideal.map_comap_of_surjective _ (Inf29.φ_surjective _ i),
      Ideal.map_comap_of_surjective _ (Inf29.φ_surjective _ i)] at h2
    exact Subtype.ext h2
  rcases (Ideal.comap_isPrime (ψ 𝒪 π) p₁).mem_or_mem hXY with h | h
  · exact main 0 (dvd_mul_right _ _) h
  · exact main 1 (dvd_mul_left _ _) h

end S_CerednikDrinfeld_FormalOmega_chartERing_infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_chartERing_infinite_setOf_le_of_mem_minimalPrimes_quotient_level_zero (solution)
