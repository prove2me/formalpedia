-- Prove2me | solution 1 for FourExp.trdeg_one_presentation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T06:32:53.887529+00:00
-- url     : https://prove2.me/submissions/5270056a-4570-4b96-8f47-d91cdfdc74a1

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Polynomial

namespace FourExpPres

lemma omega_transcendental (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂])
    (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j))) :
    Transcendental ℚ (x₁ * y₁) := by
  have hx1 : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hy1 : y₁ ≠ 0 := by simpa using hy.ne_zero 0
  intro ha
  exact DiazModulus.hermite_lindemann_holds (x₁ * y₁) (mul_ne_zero hx1 hy1) ha (by simpa using hexp 0 0)

/-- Algebraic over `ℚ[ω]` implies algebraic over `ℚ(ω)`. -/
lemma isAlgebraic_field_of_algebra {ω z : ℂ} (h : IsAlgebraic (Algebra.adjoin ℚ ({ω} : Set ℂ)) z) :
    IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) z := by
  obtain ⟨p, hp0, hpz⟩ := h
  have hle : Algebra.adjoin ℚ ({ω} : Set ℂ) ≤ (IntermediateField.adjoin ℚ ({ω} : Set ℂ)).toSubalgebra :=
    IntermediateField.algebra_adjoin_le_adjoin ℚ _
  let ι : Algebra.adjoin ℚ ({ω} : Set ℂ) →+* IntermediateField.adjoin ℚ ({ω} : Set ℂ) :=
    (Subalgebra.inclusion hle).toRingHom
  have hι : Function.Injective ι := Subalgebra.inclusion_injective hle
  refine ⟨p.map ι, (Polynomial.map_ne_zero_iff hι).2 hp0, ?_⟩
  have hcomp : (algebraMap (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) ℂ).comp ι
      = algebraMap (Algebra.adjoin ℚ ({ω} : Set ℂ)) ℂ := by
    ext r; rfl
  rw [aeval_def, eval₂_map, hcomp]
  rwa [aeval_def] at hpz

/-- In an algebra of transcendence degree at most one, everything is algebraic over `ℚ(ω)`. -/
lemma algebraic_over_omega (S : Set ℂ) (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ S) ≤ 1)
    {ω z : ℂ} (hωS : ω ∈ Algebra.adjoin ℚ S) (hzS : z ∈ Algebra.adjoin ℚ S)
    (hω : Transcendental ℚ ω) :
    IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) z := by
  by_contra hz
  have hind : AlgebraicIndependent ℚ (fun _ : Unit => ω) :=
    (algebraicIndependent_singleton_iff ()).2 hω
  have htrans : Transcendental (Algebra.adjoin ℚ (Set.range fun _ : Unit => ω)) z := by
    intro ha
    rw [Set.range_const] at ha
    exact hz (isAlgebraic_field_of_algebra ha)
  have hopt := (hind.option_iff_transcendental z).2 htrans
  let v : Option Unit → Algebra.adjoin ℚ S := fun o => o.elim ⟨z, hzS⟩ (fun _ => ⟨ω, hωS⟩)
  have hv : AlgebraicIndependent ℚ v := by
    refine AlgebraicIndependent.of_comp (Algebra.adjoin ℚ S).val ?_
    convert hopt using 1
    funext o
    cases o <;> rfl
  have hcard := hv.cardinalMk_le_trdeg
  have h2 : Cardinal.mk (Option Unit) = 2 := by simp
  rw [h2] at hcard
  have := hcard.trans htr
  norm_num at this

/-- Evaluation of `A ∈ ℤ[X][Y]` at `(ω, ω₁)`, as a ring hom. -/
noncomputable def evH (ω ω₁ : ℂ) : Polynomial (Polynomial ℤ) →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁

/-- `y` has a presentation `y · D = E` at `(ω, ω₁)` with `D ≠ 0` there. -/
def Presentable (ω ω₁ y : ℂ) : Prop :=
  ∃ D E : Polynomial (Polynomial ℤ), evH ω ω₁ D ≠ 0 ∧ y * evH ω ω₁ D = evH ω ω₁ E

lemma presentable_ev (ω ω₁ : ℂ) (A : Polynomial (Polynomial ℤ)) : Presentable ω ω₁ (evH ω ω₁ A) :=
  ⟨1, A, by simp, by simp⟩

lemma presentable_add {ω ω₁ y z : ℂ} (hy : Presentable ω ω₁ y) (hz : Presentable ω ω₁ z) :
    Presentable ω ω₁ (y + z) := by
  obtain ⟨D₁, E₁, h₁, e₁⟩ := hy
  obtain ⟨D₂, E₂, h₂, e₂⟩ := hz
  refine ⟨D₁ * D₂, E₁ * D₂ + E₂ * D₁, by simp [h₁, h₂], ?_⟩
  simp only [map_mul, map_add]
  rw [← e₁, ← e₂]
  ring

lemma presentable_mul {ω ω₁ y z : ℂ} (hy : Presentable ω ω₁ y) (hz : Presentable ω ω₁ z) :
    Presentable ω ω₁ (y * z) := by
  obtain ⟨D₁, E₁, h₁, e₁⟩ := hy
  obtain ⟨D₂, E₂, h₂, e₂⟩ := hz
  refine ⟨D₁ * D₂, E₁ * E₂, by simp [h₁, h₂], ?_⟩
  simp only [map_mul]
  rw [← e₁, ← e₂]
  ring

lemma common_denominator {ω ω₁ : ℂ} {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (h : ∀ i, Presentable ω ω₁ (f i)) :
    ∃ D : Polynomial (Polynomial ℤ), evH ω ω₁ D ≠ 0 ∧
      ∀ i, ∃ E : Polynomial (Polynomial ℤ), f i * evH ω ω₁ D = evH ω ω₁ E := by
  classical
  choose D E hD hE using h
  refine ⟨∏ i, D i, ?_, fun i => ⟨E i * ∏ j ∈ Finset.univ.erase i, D j, ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hD i
  · rw [map_prod, map_mul, map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => evH ω ω₁ (D j))
      (Finset.mem_univ i), ← mul_assoc, hE i]

/-- A rational polynomial becomes integral after multiplying by a positive integer. -/
lemma exists_int_scaled (p : ℚ[X]) :
    ∃ n : ℕ, 0 < n ∧ ∃ q : ℤ[X], q.map (Int.castRingHom ℚ) = C (n : ℚ) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨n₁, hn₁, q₁, e₁⟩ := hp
    obtain ⟨n₂, hn₂, q₂, e₂⟩ := hq
    refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, C (n₂ : ℤ) * q₁ + C (n₁ : ℤ) * q₂, ?_⟩
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, C_mul]
    ring
  | monomial k a =>
    refine ⟨a.den, a.den_pos, monomial k a.num, ?_⟩
    rw [Polynomial.map_monomial, C_mul_monomial]
    congr 1
    simp [Rat.mul_den_eq_num]

lemma evH_C (ω ω₁ : ℂ) (q : ℤ[X]) :
    evH ω ω₁ (C q) = aeval ω (q.map (Int.castRingHom ℚ)) := by
  simp only [evH, Polynomial.coe_eval₂RingHom, eval₂_C, aeval_def, eval₂_map]
  congr 1

/-- Every element of `ℚ(ω)` is presentable. -/
lemma presentable_of_mem {ω ω₁ y : ℂ} (hy : y ∈ IntermediateField.adjoin ℚ ({ω} : Set ℂ)) :
    Presentable ω ω₁ y := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hy
  obtain ⟨r, s, rfl⟩ := hy
  obtain ⟨n₁, hn₁, q₁, e₁⟩ := exists_int_scaled r
  obtain ⟨n₂, hn₂, q₂, e₂⟩ := exists_int_scaled s
  by_cases hs : aeval ω s = 0
  · rw [hs, div_zero]
    exact ⟨1, 0, by simp, by simp⟩
  refine ⟨C (C (n₁ : ℤ) * q₂), C (C (n₂ : ℤ) * q₁), ?_, ?_⟩
  · rw [evH_C, Polynomial.map_mul, e₂, Polynomial.map_C]
    simp only [eq_intCast, Int.cast_natCast, map_mul, aeval_C]
    have h1 : (algebraMap ℚ ℂ) (n₁ : ℚ) ≠ 0 := by simp [hn₁.ne']
    have h2 : (algebraMap ℚ ℂ) (n₂ : ℚ) ≠ 0 := by simp [hn₂.ne']
    exact mul_ne_zero h1 (mul_ne_zero h2 hs)
  · rw [evH_C, evH_C, Polynomial.map_mul, Polynomial.map_mul, e₁, e₂, Polynomial.map_C,
      Polynomial.map_C]
    simp only [eq_intCast, Int.cast_natCast, map_mul, aeval_C]
    field_simp

lemma presentable_pow {ω ω₁ θ : ℂ} (hθ : Presentable ω ω₁ θ) (n : ℕ) :
    Presentable ω ω₁ (θ ^ n) := by
  induction n with
  | zero => simpa using presentable_ev ω ω₁ 1
  | succ n ih => rw [pow_succ]; exact presentable_mul ih hθ

/-- If `θ` is presentable, so is every `aeval θ p` with `p ∈ ℚ(ω)[X]`. -/
lemma presentable_aeval {ω ω₁ θ : ℂ} (hθ : Presentable ω ω₁ θ)
    (p : Polynomial (IntermediateField.adjoin ℚ ({ω} : Set ℂ))) :
    Presentable ω ω₁ (aeval θ p) := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact presentable_of_mem a.2
  | add p q hp hq => rw [map_add]; exact presentable_add hp hq
  | monomial n a _ =>
    rw [map_mul, map_pow, aeval_C, aeval_X]
    exact presentable_mul (presentable_of_mem a.2) (presentable_pow hθ (n + 1))

/-- Finitely many elements algebraic over `F` lie in `F[θ]` for one integral `θ`. -/
lemma exists_primitive (F : IntermediateField ℚ ℂ) (S : Finset ℂ) (hS : ∀ z ∈ S, IsAlgebraic F z) :
    ∃ θ : ℂ, IsIntegral F θ ∧ ∀ z ∈ S, ∃ p : Polynomial F, aeval θ p = z := by
  classical
  set E := IntermediateField.adjoin F (S : Set ℂ) with hE
  haveI : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hS z hz).isIntegral
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  have hαint : IsIntegral F α := .of_finite F α
  refine ⟨(α : ℂ), hαint.map E.val, fun z hz => ?_⟩
  have hzE : (⟨z, IntermediateField.subset_adjoin F _ hz⟩ : E) ∈ IntermediateField.adjoin F ({α} : Set E) := by
    rw [hα]; exact IntermediateField.mem_top
  have hsub : (IntermediateField.adjoin F ({α} : Set E)).toSubalgebra = Algebra.adjoin F {α} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hαint.isAlgebraic
  have hmem : (⟨z, IntermediateField.subset_adjoin F _ hz⟩ : E) ∈ Algebra.adjoin F {α} := by
    rw [← hsub]; exact hzE
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, ?_⟩
  have := congrArg E.val hp
  simpa [Polynomial.aeval_algHom_apply] using this

lemma eval_int_eq_aeval (ω : ℂ) (q : ℤ[X]) :
    Polynomial.eval₂ (Int.castRingHom ℂ) ω q = aeval ω (q.map (Int.castRingHom ℚ)) := by
  rw [aeval_def, eval₂_map]
  congr 1

/-- The embedding `ℤ[X] → ℚ(ω)`, `q ↦ q(ω)`. -/
noncomputable def phiω (ω : ℂ) : ℤ[X] →+* IntermediateField.adjoin ℚ ({ω} : Set ℂ) :=
  Polynomial.eval₂RingHom (Int.castRingHom _) ⟨ω, IntermediateField.mem_adjoin_simple_self ℚ ω⟩

lemma phi_eval (ω : ℂ) :
    (algebraMap (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) ℂ).comp (phiω ω)
      = Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [phiω]
  · simp [phiω]

lemma phi_coe (ω : ℂ) (q : ℤ[X]) :
    ((phiω ω q : IntermediateField.adjoin ℚ ({ω} : Set ℂ)) : ℂ) = aeval ω (q.map (Int.castRingHom ℚ)) := by
  rw [← eval_int_eq_aeval]
  exact RingHom.congr_fun (phi_eval ω) q

lemma phi_injective {ω : ℂ} (hω : Transcendental ℚ ω) : Function.Injective (phiω ω) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra hq0
  apply hω
  refine ⟨q.map (Int.castRingHom ℚ), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hq0, ?_⟩
  rw [← phi_coe, hq]
  rfl

lemma int_frac {ω : ℂ} (y : IntermediateField.adjoin ℚ ({ω} : Set ℂ)) :
    ∃ r s : ℤ[X], phiω ω s ≠ 0 ∧ y * phiω ω s = phiω ω r := by
  have hy := y.2
  rw [IntermediateField.mem_adjoin_simple_iff] at hy
  obtain ⟨r, s, hrs⟩ := hy
  obtain ⟨n₁, hn₁, q₁, e₁⟩ := exists_int_scaled r
  obtain ⟨n₂, hn₂, q₂, e₂⟩ := exists_int_scaled s
  have h1 : (algebraMap ℚ ℂ) (n₁ : ℚ) ≠ 0 := by simp [hn₁.ne']
  have h2 : (algebraMap ℚ ℂ) (n₂ : ℚ) ≠ 0 := by simp [hn₂.ne']
  by_cases hs : aeval ω s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    apply Subtype.ext
    simp [hrs, hs]
  refine ⟨C (n₂ : ℤ) * q₁, C (n₁ : ℤ) * q₂, ?_, ?_⟩
  · intro h0
    have h := congrArg (fun z : IntermediateField.adjoin ℚ ({ω} : Set ℂ) => (z : ℂ)) h0
    simp only [IntermediateField.coe_zero] at h
    rw [phi_coe] at h
    simp only [Polynomial.map_mul, e₂, Polynomial.map_C, eq_intCast, Int.cast_natCast,
      map_mul, aeval_C, Polynomial.map_natCast, map_natCast] at h
    exact mul_ne_zero h1 (mul_ne_zero h2 hs) h
  · apply Subtype.ext
    rw [IntermediateField.coe_mul, phi_coe, phi_coe]
    simp only [Polynomial.map_mul, e₁, e₂, Polynomial.map_C,
      eq_intCast, Int.cast_natCast, map_mul, aeval_C, hrs, Polynomial.map_natCast, map_natCast]
    field_simp

lemma evH_C_eq (ω ω₁ : ℂ) (q : ℤ[X]) :
    evH ω ω₁ (C q) = algebraMap (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) ℂ (phiω ω q) := by
  rw [evH_C]
  exact (phi_coe ω q).symm

lemma evH_X (ω ω₁ : ℂ) : evH ω ω₁ X = ω₁ := by simp [evH]

/-- A primitive element scaled into an integral generator with a monic minimal relation. -/
lemma integral_generator {ω θ : ℂ} (hω : Transcendental ℚ ω)
    (hθ : IsIntegral (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) θ) :
    ∃ (ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)), Q.Monic ∧ 0 < Q.natDegree ∧ evH ω ω₁ Q = 0 ∧
      (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → evH ω ω₁ A = 0 → A = 0) ∧
      Presentable ω ω₁ θ := by
  classical
  set F := IntermediateField.adjoin ℚ ({ω} : Set ℂ) with hF
  set m := minpoly F θ with hm
  set d := m.natDegree with hd
  have hmon : m.Monic := minpoly.monic hθ
  have hdpos : 0 < d := minpoly.natDegree_pos hθ
  choose r s hs hrs using fun k : ℕ => int_frac (ω := ω) (m.coeff k)
  set v : ℤ[X] := ∏ k : Fin d, s k with hv
  have hv0 : phiω ω v ≠ 0 := by
    rw [hv, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hs k
  set t : Fin d → ℤ[X] := fun k => r k * (∏ j ∈ Finset.univ.erase k, s j) * v ^ (d - 1 - k) with ht
  set Q : Polynomial (Polynomial ℤ) := X ^ d + ∑ k : Fin d, C (t k) * X ^ (k : ℕ) with hQ
  set c : ℂ := algebraMap F ℂ (phiω ω v) with hc
  set ω₁ : ℂ := c * θ with hω₁
  have hc0 : c ≠ 0 := by
    rw [hc]; exact (map_ne_zero_iff _ (algebraMap F ℂ).injective).2 hv0
  have hdeg : (∑ k : Fin d, C (t k) * X ^ (k : ℕ)).degree < (d : WithBot ℕ) := Polynomial.degree_sum_fin_lt t
  have hQmon : Q.Monic := Polynomial.monic_X_pow_add hdeg
  have hQdeg : Q.natDegree = d := by
    rw [hQ, Polynomial.natDegree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.natDegree_X_pow]
  refine ⟨ω₁, Q, hQmon, by rw [hQdeg]; exact hdpos, ?_, ?_, ?_⟩
  · -- `Q(ω, ω₁) = c^d · m(θ) = 0`
    have hsum : aeval θ m = 0 := minpoly.aeval F θ
    rw [hmon.as_sum] at hsum
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at hsum
    rw [← Fin.sum_univ_eq_sum_range (fun i => algebraMap F ℂ (m.coeff i) * θ ^ i) d] at hsum
    have hEC : ∀ q : ℤ[X], evH ω ω₁ (C q) = algebraMap F ℂ (phiω ω q) := fun q => evH_C_eq ω ω₁ q
    have key : ∀ k : Fin d, evH ω ω₁ (C (t k)) * ω₁ ^ (k : ℕ)
        = c ^ d * (algebraMap F ℂ (m.coeff k) * θ ^ (k : ℕ)) := by
      intro k
      have hk : (k : ℕ) < d := k.2
      have hrk : algebraMap F ℂ (phiω ω (r k))
          = algebraMap F ℂ (m.coeff k) * algebraMap F ℂ (phiω ω (s k)) := by
        rw [← map_mul, hrs k]
      have hvprod : algebraMap F ℂ (phiω ω (s k))
          * algebraMap F ℂ (phiω ω (∏ j ∈ Finset.univ.erase k, s j)) = c := by
        rw [← map_mul, ← map_mul, hc, hv,
          Finset.mul_prod_erase Finset.univ (fun j : Fin d => s j) (Finset.mem_univ k)]
      have htk : evH ω ω₁ (C (t k)) = algebraMap F ℂ (phiω ω (r k))
          * algebraMap F ℂ (phiω ω (∏ j ∈ Finset.univ.erase k, s j)) * c ^ (d - 1 - (k : ℕ)) := by
        rw [hEC, ht]
        simp only [map_mul, map_pow, hc]
      have hexp : c ^ d = c * c ^ (d - 1 - (k : ℕ)) * c ^ (k : ℕ) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [htk, hrk, hω₁, mul_pow, hexp, ← hvprod]
      ring
    calc evH ω ω₁ Q = ω₁ ^ d + ∑ k : Fin d, evH ω ω₁ (C (t k)) * ω₁ ^ (k : ℕ) := by
          simp only [hQ, map_add, map_pow, evH_X, map_sum, map_mul]
      _ = c ^ d * (θ ^ d + ∑ k : Fin d, algebraMap F ℂ (m.coeff k) * θ ^ (k : ℕ)) := by
          rw [Finset.sum_congr rfl fun k _ => key k, ← Finset.mul_sum, hω₁, mul_pow]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  · -- minimality
    intro A hA hA0
    rw [hQdeg] at hA
    have hB : aeval ω₁ (A.map (phiω ω)) = evH ω ω₁ A := by
      rw [aeval_def, eval₂_map, phi_eval]
      rfl
    have hint : IsIntegral F ω₁ := (isIntegral_algebraMap (x := phiω ω v)).mul hθ
    have hadj : IntermediateField.adjoin F ({ω₁} : Set ℂ) = IntermediateField.adjoin F ({θ} : Set ℂ) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F θ)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have hθeq : θ = algebraMap F ℂ (phiω ω v)⁻¹ * ω₁ := by
          rw [hω₁, hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hv0, map_one, one_mul]
        rw [hθeq]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F ω₁)
    have hdeg1 : (minpoly F ω₁).natDegree = d := by
      rw [← IntermediateField.adjoin.finrank hint, hadj, IntermediateField.adjoin.finrank hθ]
    by_contra hA0'
    have hB0 : A.map (phiω ω) ≠ 0 := (Polynomial.map_ne_zero_iff (phi_injective hω)).2 hA0'
    have h1 := minpoly.degree_le_of_ne_zero F ω₁ hB0 (hB.trans hA0)
    have h2 := Polynomial.natDegree_le_natDegree h1
    rw [hdeg1, Polynomial.natDegree_map_eq_of_injective (phi_injective hω)] at h2
    omega
  · -- `θ · v(ω) = ω₁`
    refine ⟨C v, X, by rw [evH_C_eq]; exact hc0, ?_⟩
    rw [evH_C_eq, evH_X, hω₁, ← hc, mul_comm]

end FourExpPres

open FourExpPres in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1) :
    ∃ ω ω₁ : ℂ, Transcendental ℚ ω ∧ ∃ Q : Polynomial (Polynomial ℤ),
        Q.Monic ∧ 0 < Q.natDegree ∧ Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
        (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
        ∃ (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ)),
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧ (∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i)) ∧
          (∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) ∧
          (∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) := by
  classical
  have hω : Transcendental ℚ (x₁ * y₁) := omega_transcendental x₁ x₂ y₁ y₂ hx hy hexp
  have hS : ∀ z ∈ ({x₁, x₂, y₁, y₂} : Set ℂ), z ∈ Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ) :=
    fun z hz => Algebra.subset_adjoin hz
  have hωmem : x₁ * y₁ ∈ Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ) :=
    mul_mem (hS _ (by simp)) (hS _ (by simp))
  have halg : ∀ z ∈ ({x₁, x₂, y₁, y₂} : Set ℂ),
      IsAlgebraic (IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ)) z :=
    fun z hz => algebraic_over_omega _ htr hωmem (hS z hz) hω
  have halgE : ∀ i j : Fin 2, IsAlgebraic (IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ))
      (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)) := fun i j =>
    IsAlgebraic.tower_top (L := IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ)) (hexp i j)
  set Gen : Finset ℂ := {x₁, x₂, y₁, y₂} ∪
    Finset.univ.image (fun p : Fin 2 × Fin 2 => Complex.exp (![x₁, x₂] p.1 * ![y₁, y₂] p.2)) with hGen
  obtain ⟨θ, hθ, hgen⟩ := exists_primitive (IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ)) Gen (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact halg z (by simpa using h)
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
      exact halgE p.1 p.2)
  obtain ⟨ω₁, Q, hQm, hQd, hQroot, hQmin, hθpres⟩ := integral_generator hω hθ
  have hpres : ∀ z ∈ Gen, Presentable (x₁ * y₁) ω₁ z := fun z hz => by
    obtain ⟨p, rfl⟩ := hgen z hz
    exact presentable_aeval hθpres p
  have hxmem : ∀ i : Fin 2, ![x₁, x₂] i ∈ Gen := fun i => by fin_cases i <;> simp [hGen]
  have hymem : ∀ j : Fin 2, ![y₁, y₂] j ∈ Gen := fun j => by fin_cases j <;> simp [hGen]
  have hemem : ∀ i j : Fin 2, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) ∈ Gen := fun i j =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  let f : Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 × Fin 2)) → ℂ := fun o =>
    Sum.elim (fun i => ![x₁, x₂] i)
      (Sum.elim (fun j => ![y₁, y₂] j) (fun p => Complex.exp (![x₁, x₂] p.1 * ![y₁, y₂] p.2))) o
  have hf : ∀ o, Presentable (x₁ * y₁) ω₁ (f o) := by
    rintro (i | j | p)
    · exact hpres _ (hxmem i)
    · exact hpres _ (hymem j)
    · exact hpres _ (hemem p.1 p.2)
  obtain ⟨D, hD, hE⟩ := common_denominator f hf
  choose E hE using hE
  exact ⟨x₁ * y₁, ω₁, hω, Q, hQm, hQd, hQroot, hQmin, D, fun i => E (.inl i), fun j => E (.inr (.inl j)),
    fun i j => E (.inr (.inr (i, j))), hD, fun i => hE (.inl i), fun j => hE (.inr (.inl j)),
    fun i j => hE (.inr (.inr (i, j)))⟩
