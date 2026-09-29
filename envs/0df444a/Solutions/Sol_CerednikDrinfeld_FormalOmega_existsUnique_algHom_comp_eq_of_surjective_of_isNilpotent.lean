-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/952e9da1-bc03-5574-9d19-8c8a0fa790c1

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalOmega_charP_residue_and_forall_exists_pow_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_ringHom_ext_of_isNilpotent_natCast
import Theorems.Thm_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent

set_option autoImplicit false

namespace LegLiftAsm

open Function

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
  {W : Type} [CommRing W]
  {B : Type} [CommRing B] [Algebra 𝒪 B] {B₀ : Type} [CommRing B₀] [Algebra 𝒪 B₀]

theorem ringHom_ext_of_surjective {R S T : Type} [CommRing R] [CommRing S] [Semiring T] (f : R →+* S) (hf : Surjective f)
    (g₁ g₂ : S →+* T) (h : g₁.comp f = g₂.comp f) : g₁ = g₂ :=
  RingHom.ext fun s => by obtain ⟨x, rfl⟩ := hf s; exact congrArg (fun φ : R →+* T => φ x) h

theorem core (r : ℕ) (π : 𝒪) (hrπ : (r : 𝒪) ∈ Ideal.span {π})

    (hW1 : ∀ (C : Type) [CommRing C], IsNilpotent ((r : ℕ) : C) → ∀ f g : 𝒪 →+* C, f = g)

    (N : ℕ) (fN : W →+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N}) (hfN : Surjective fN)
    (hker : ∀ w : W, fN w = 0 → ∃ w' : W, w = (r : W) ^ N * w')

    (p : B →ₐ[𝒪] B₀)
    (hW3 : ∀ g₀ : W →+* B₀, ∃! g : W →+* B, p.toRingHom.comp g = g₀)

    (hB : algebraMap 𝒪 B π ^ N = 0) (ψ₀ : Onr →ₐ[𝒪] B₀) :
    ∃! ψ : Onr →ₐ[𝒪] B, p.comp ψ = ψ₀ := by
  classical

  have hrB : IsNilpotent ((r : ℕ) : B) := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    refine ⟨N, ?_⟩
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hB, mul_zero]
  have hrNB : ((r : ℕ) : B) ^ N = 0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hB, mul_zero]
  have hB₀ : algebraMap 𝒪 B₀ π ^ N = 0 := by
    rw [← p.commutes, ← map_pow, hB, map_zero]

  have hψ₀I : ∀ a ∈ Ideal.span {algebraMap 𝒪 Onr π ^ N}, ψ₀ a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, ψ₀.commutes, hB₀, mul_zero]
  let ψ₀' : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →ₐ[𝒪] B₀ := Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I

  let g₀ : W →+* B₀ := ψ₀'.toRingHom.comp fN
  obtain ⟨g, hg, hguniq⟩ := hW3 g₀

  have hgker : ∀ w ∈ RingHom.ker fN, g w = 0 := by
    intro w hw
    obtain ⟨w', rfl⟩ := hker w ((RingHom.mem_ker).1 hw)
    rw [map_mul, map_pow, map_natCast, hrNB, zero_mul]

  let e : W ⧸ RingHom.ker fN ≃+* Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} := RingHom.quotientKerEquivOfSurjective hfN
  let gbar : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →+* B := (Ideal.Quotient.lift (RingHom.ker fN) g hgker).comp e.symm.toRingHom
  have hgbar : gbar.comp fN = g := by
    apply RingHom.ext; intro w
    show (Ideal.Quotient.lift (RingHom.ker fN) g hgker) (e.symm (fN w)) = g w
    rw [← RingHom.quotientKerEquivOfSurjective_apply_mk hfN w]
    show (Ideal.Quotient.lift (RingHom.ker fN) g hgker) (e.symm (e (Ideal.Quotient.mk _ w))) = g w
    rw [RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

  let ψr : Onr →+* B := gbar.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}))
  have hlin : ψr.comp (algebraMap 𝒪 Onr) = algebraMap 𝒪 B := hW1 B hrB _ _
  let ψ : Onr →ₐ[𝒪] B :=
    { toRingHom := ψr
      commutes' := fun c => congrArg (fun φ : 𝒪 →+* B => φ c) hlin }

  have hpgbar : p.toRingHom.comp gbar = ψ₀'.toRingHom := by
    apply ringHom_ext_of_surjective fN hfN
    rw [RingHom.comp_assoc, hgbar, hg]
  have hpψ : p.comp ψ = ψ₀ := by
    apply AlgHom.ext; intro x
    have h1 := congrArg (fun φ : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →+* B₀ => φ (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)) hpgbar
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [AlgHom.comp_apply]
    refine h1.trans ?_
    show (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x) = ψ₀ x
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; rfl
  refine ⟨ψ, hpψ, ?_⟩

  intro ψ' hψ'
  have hψ'I : ∀ a ∈ Ideal.span {algebraMap 𝒪 Onr π ^ N}, ψ' a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, ψ'.commutes, hB, mul_zero]
  let ψ'' : Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π ^ N} →ₐ[𝒪] B := Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I
  have hψ''mk : ψ''.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N})) = ψ'.toRingHom := by
    apply RingHom.ext; intro x
    show (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x) = ψ' x
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]; rfl

  have hg' : p.toRingHom.comp (ψ''.toRingHom.comp fN) = g₀ := by
    apply RingHom.ext; intro w
    obtain ⟨x, hx⟩ : ∃ x : Onr, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x = fN w := Ideal.Quotient.mk_surjective (fN w)
    show p (ψ'' (fN w)) = ψ₀' (fN w)
    rw [← hx]
    show p ((Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ' hψ'I) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)) = (Ideal.Quotient.liftₐ (Ideal.span {algebraMap 𝒪 Onr π ^ N}) ψ₀ hψ₀I) (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}) x)
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact congrArg (fun φ : Onr →ₐ[𝒪] B₀ => φ x) hψ'
  have hgg : ψ''.toRingHom.comp fN = g := hguniq _ hg'
  have hψ''gbar : ψ''.toRingHom = gbar := by
    apply ringHom_ext_of_surjective fN hfN
    rw [hgg, hgbar]
  apply AlgHom.ext; intro x
  have := congrArg (fun φ : Onr →+* B => φ x) (hψ''mk.symm.trans (congrArg (fun φ => RingHom.comp φ (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 Onr π ^ N}))) hψ''gbar))
  exact this

end LegLiftAsm

open LegLiftAsm in
theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π))
    (hp : Function.Surjective p) (hsq : ∀ s t : B, p s = 0 → p t = 0 → s * t = 0)
    (ψ₀ : Onr →ₐ[𝒪] B₀) :
    ∃! ψ : Onr →ₐ[𝒪] B, p.comp ψ = ψ₀ := by
  classical

  obtain ⟨N, hN⟩ := hB

  have hrπ : ((r : ℕ) : 𝒪) ∈ Ideal.span {π} := by rw [← hunr]; exact Ideal.mem_span_singleton_self _
  have hrB : IsNilpotent ((r : ℕ) : B) := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hrπ
    refine ⟨N, ?_⟩
    rw [← map_natCast (algebraMap 𝒪 B), ← ha, map_mul, mul_pow, hN, mul_zero]

  haveI hmax : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max
  letI : Field (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) := Ideal.Quotient.field _
  obtain ⟨hchar, hroot⟩ := CerednikDrinfeld.FormalOmega.charP_residue_and_forall_exists_pow_eq 𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
  haveI := hchar
  haveI : PerfectRing (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) r :=
    PerfectRing.ofSurjective _ r (fun a => by obtain ⟨b, hb⟩ := hroot a; exact ⟨b, by rw [frobenius_def]; exact hb⟩)

  obtain ⟨fN, -, hfN, hker⟩ := CerednikDrinfeld.FormalOmega.exists_ringHom_wittVector_surjective_and_ker_eq_of_ker_eq_span 𝒪 hdvr π hπ hcomplete hres hunr Onr hOnr_complete hOnr_max hOnr_alg hOnr_closed
    (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective Ideal.mk_ker N

  exact core r π hrπ
    (fun C _ hC f g => CerednikDrinfeld.FormalOmega.ringHom_ext_of_isNilpotent_natCast 𝒪 hdvr π hπ hcomplete hres hunr C hC f g)
    N fN hfN
    (fun w hw => by
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 ((hker w).1 hw)
      exact ⟨a, by rw [mul_comm]; exact ha.symm⟩)
    p
    (fun g₀ => WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent r (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π}) B B₀ p.toRingHom hp hsq hrB g₀)
    hN ψ₀

end S_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_algHom_comp_eq_of_surjective_of_isNilpotent (solution)
