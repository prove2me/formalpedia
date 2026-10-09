-- Prove2me | solution 1 for DiazModulus.laurent_hull_config_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-08T16:42:32.203706+00:00
-- url     : https://prove2.me/submissions/b542ec4f-7fee-48c2-a41a-670349319505

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_polynomial_submodule_trailing_degrees_card

open Complex ComplexConjugate

/-! # Configurations in a Laurent hull `Σ_{s ∈ S} K uˢ`

Let `u` be transcendental over `K` and `S` a finite set of integers. A `p × q` configuration
(`x` and `y` linearly independent, all products `xᵢ yⱼ` in `Σ_{s ∈ S} K uˢ`) exists exactly when
`S` contains a sumset `A + B` with `|A| = p`, `|B| = q`.

If `A + B ⊆ S`, take `xᵢ = u^{aᵢ}`, `yⱼ = u^{bⱼ}`: distinct integer powers of a transcendental
element are linearly independent (shift them into polynomials), and `u^{a} u^{b} = u^{a+b}`.

Conversely, pick `N` with `S + N ⊆ ℕ` and polynomials `Pᵢⱼ`, supported on `S + N`, with
`Pᵢⱼ(u) = uᴺ xᵢ yⱼ`. The spans `V` of the `Pᵢ₀` and `W` of the `P₀ⱼ` have dimensions `p` and `q`,
so (`polynomial_submodule_trailing_degrees_card`) they have exactly `p` and `q` orders at `0`.
For `f ∈ V`, `g ∈ W` one has `f g = P₀₀ h` with `h` a combination of the `Pᵢⱼ`, because both
sides agree at `u`. Comparing orders, `ord f + ord g − ord P₀₀ − N ∈ S`; this gives `A` and `B`.
-/

namespace R6_laurent

open DiazModulus Polynomial

section supp

variable {F : Type*} [Field F]

/-- The polynomials whose exponents all lie in `E`. -/
def supp (E : Set ℕ) : Submodule F F[X] where
  carrier := {P | ∀ n ∉ E, P.coeff n = 0}
  add_mem' ha hb n hn := by rw [coeff_add, ha n hn, hb n hn, add_zero]
  zero_mem' n _ := coeff_zero n
  smul_mem' c P hP n hn := by rw [coeff_smul, hP n hn, smul_zero]

theorem X_pow_mem_supp {E : Set ℕ} {m : ℕ} (hm : m ∈ E) : (X ^ m : F[X]) ∈ supp E := by
  intro n hn
  rw [coeff_X_pow, if_neg (by rintro rfl; exact hn hm)]

theorem natTrailingDegree_mem {E : Set ℕ} {P : F[X]} (hP : P ∈ supp E) (h0 : P ≠ 0) :
    P.natTrailingDegree ∈ E := by
  by_contra h
  exact trailingCoeff_nonzero_iff_nonzero.2 h0 (hP _ h)

end supp

variable {K : Subfield ℂ} {u : ℂ}

theorem ne_zero_of_transcendental (hT : Transcendental K u) : u ≠ 0 := by
  rintro rfl
  exact hT isAlgebraic_zero

theorem aeval_injective (hT : Transcendental K u) : Function.Injective (aeval (R := K) u) :=
  transcendental_iff_injective.1 hT

theorem li_congr {ι : Type*} {v w : ι → ℂ} (h : LinearIndependent K v) (e : ∀ i, v i = w i) :
    LinearIndependent K w := by
  rwa [funext e] at h

/-- Distinct integer powers of a transcendental element are linearly independent. -/
theorem linearIndependent_zpow (hT : Transcendental K u) {ι : Type*} [Fintype ι] (e : ι → ℤ)
    (he : Function.Injective e) : LinearIndependent K (fun i => u ^ e i) := by
  have hu0 := ne_zero_of_transcendental hT
  set N : ℕ := ∑ i, (e i).natAbs
  have hN : ∀ i, 0 ≤ e i + N := fun i => by
    have : (e i).natAbs ≤ N := Finset.single_le_sum (f := fun i => (e i).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  let n : ι → ℕ := fun i => (e i + N).toNat
  have hn : Function.Injective n := fun i j h => he (by
    have h' : (e i + N).toNat = (e j + N).toNat := h
    have := hN i; have := hN j
    omega)
  have h1 : LinearIndependent K (fun m : ℕ => u ^ m) := by
    have h0 := (basisMonomials K).linearIndependent.map' (aeval u).toLinearMap
      (LinearMap.ker_eq_bot.2 (aeval_injective hT))
    have e0 : (⇑(aeval u).toLinearMap ∘ ⇑(basisMonomials K)) = fun m : ℕ => u ^ m := by
      funext m; simp
    rw [e0] at h0
    exact h0
  have huN : (u ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hu0)
  have h2 := (h1.comp n hn).map' (LinearMap.mulLeft K (u ^ N)⁻¹)
    (LinearMap.ker_eq_bot.2 (mul_right_injective₀ huN))
  refine li_congr h2 fun i => ?_
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, n]
  rw [← zpow_natCast u (e i + N).toNat, Int.toNat_of_nonneg (hN i), zpow_add₀ hu0, zpow_natCast]
  field_simp

/-- The shifted support `S + N`, as a set of naturals. -/
def shift (S : Finset ℤ) (N : ℕ) : Set ℕ := {n | (n : ℤ) - N ∈ S}

/-- `uᴺ v` is the value at `u` of a polynomial supported on `S + N`. -/
theorem exists_poly (hu0 : u ≠ 0) {S : Finset ℤ} {N : ℕ} (hN : ∀ s ∈ S, -(N : ℤ) ≤ s) {v : ℂ}
    (hv : v ∈ Submodule.span K ((fun s : ℤ => u ^ s) '' (S : Set ℤ))) :
    ∃ P ∈ supp (F := K) (shift S N), aeval u P = u ^ N * v := by
  let L : K[X] →ₗ[K] ℂ := LinearMap.mulLeft K (u ^ N)⁻¹ ∘ₗ (aeval u).toLinearMap
  have hle : Submodule.span K ((fun s : ℤ => u ^ s) '' (S : Set ℤ)) ≤
      (supp (shift S N)).map L := by
    rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    have hs' := hN s hs
    have hs0 : 0 ≤ s + N := by omega
    refine ⟨X ^ (s + N).toNat, X_pow_mem_supp (by
      simp only [shift, Set.mem_ofPred_eq]; rw [Int.toNat_of_nonneg hs0]; simpa using hs), ?_⟩
    simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, aeval_X_pow]
    rw [← zpow_natCast u (s + N).toNat, Int.toNat_of_nonneg hs0, zpow_add₀ hu0, zpow_natCast]
    field_simp
  obtain ⟨P, hP, hPv⟩ := hle hv
  refine ⟨P, hP, ?_⟩
  simp only [L, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply] at hPv
  rw [← hPv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_mul]

end R6_laurent

open DiazModulus R6_laurent Polynomial Pointwise in
theorem solution (K : Subfield ℂ) (u : ℂ) (hT : Transcendental K u)
    (S : Finset ℤ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (∃ (x : Fin p → ℂ) (y : Fin q → ℂ), LinearIndependent K x ∧ LinearIndependent K y ∧
      ∀ i j, x i * y j ∈ Submodule.span K ((fun s : ℤ => u ^ s) '' (S : Set ℤ))) ↔
    ∃ A B : Finset ℤ, A.card = p ∧ B.card = q ∧ A + B ⊆ S := by
  have hu0 := ne_zero_of_transcendental hT
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s ∈ S, -(N : ℤ) ≤ s := ⟨∑ s ∈ S, s.natAbs, fun s hs => by
      have : s.natAbs ≤ ∑ s ∈ S, s.natAbs :=
        Finset.single_le_sum (f := fun s => s.natAbs) (fun _ _ => Nat.zero_le _) hs
      omega⟩
    choose P hP hPe using fun i j => exists_poly (K := K) hu0 hN (hxy i j)
    let i0 : Fin p := ⟨0, by omega⟩
    let j0 : Fin q := ⟨0, by omega⟩
    -- the two spans and their dimensions
    have hcol : LinearIndependent K (fun i => P i j0) := by
      have hc : u ^ N * y j0 ≠ 0 := mul_ne_zero (pow_ne_zero _ hu0) (hy.ne_zero j0)
      have h := hx.map' (LinearMap.mulLeft K (u ^ N * y j0))
        (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))
      refine LinearIndependent.of_comp (aeval u).toLinearMap (li_congr h fun i => ?_)
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hPe, LinearMap.mulLeft_apply]
      ring
    have hrow : LinearIndependent K (fun j => P i0 j) := by
      have hc : u ^ N * x i0 ≠ 0 := mul_ne_zero (pow_ne_zero _ hu0) (hx.ne_zero i0)
      have h := hy.map' (LinearMap.mulLeft K (u ^ N * x i0))
        (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hc))
      refine LinearIndependent.of_comp (aeval u).toLinearMap (li_congr h fun j => ?_)
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply, hPe, LinearMap.mulLeft_apply]
      ring
    set V := Submodule.span K (Set.range fun i => P i j0)
    set W := Submodule.span K (Set.range fun j => P i0 j)
    have : FiniteDimensional K V := FiniteDimensional.span_of_finite K (Set.finite_range _)
    have : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range _)
    have hVc := polynomial_submodule_trailing_degrees_card K V
    have hWc := polynomial_submodule_trailing_degrees_card K W
    rw [finrank_span_eq_card hcol, Fintype.card_fin] at hVc
    rw [finrank_span_eq_card hrow, Fintype.card_fin] at hWc
    set TV := natTrailingDegree '' ((V : Set K[X]) \ {0})
    set TW := natTrailingDegree '' ((W : Set K[X]) \ {0})
    have hTV : TV.Finite := Set.finite_of_ncard_pos (by omega)
    have hTW : TW.Finite := Set.finite_of_ncard_pos (by omega)
    set ν := (P i0 j0).natTrailingDegree
    -- the order identity
    have key : ∀ a ∈ TV, ∀ b ∈ TW, (a : ℤ) + b - ν - N ∈ S := by
      rintro _ ⟨f, ⟨hfV, hf0⟩, rfl⟩ _ ⟨g, ⟨hgW, hg0⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_range_iff_exists_fun K |>.1 hfV
      obtain ⟨d, rfl⟩ := Submodule.mem_span_range_iff_exists_fun K |>.1 hgW
      set h : K[X] := ∑ i, ∑ j, (c i * d j) • P i j
      have hh : h ∈ supp (shift S N) :=
        Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hP i j)
      have he : (∑ i, c i • P i j0) * (∑ j, d j • P i0 j) = P i0 j0 * h := by
        apply aeval_injective hT
        simp only [h, map_mul, map_sum, map_smul, hPe]
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Subfield.smul_def, Subfield.coe_mul]
        ring
      have hfg : (∑ i, c i • P i j0) * (∑ j, d j • P i0 j) ≠ 0 :=
        mul_ne_zero (by simpa using hf0) (by simpa using hg0)
      rw [he] at hfg
      have hP0 : P i0 j0 ≠ 0 := left_ne_zero_of_mul hfg
      have hh0 : h ≠ 0 := right_ne_zero_of_mul hfg
      have hdeg := congrArg natTrailingDegree he
      rw [natTrailingDegree_mul (by simpa using hf0) (by simpa using hg0),
        natTrailingDegree_mul hP0 hh0] at hdeg
      have hmem : ((h.natTrailingDegree : ℕ) : ℤ) - N ∈ S := natTrailingDegree_mem hh hh0
      convert hmem using 1
      simp only [ν]
      omega
    refine ⟨hTV.toFinset.image (fun a : ℕ => (a : ℤ) - ν - N), hTW.toFinset.image (fun b : ℕ => (b : ℤ)),
      ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b hab => by
        have : (a : ℤ) - ν - N = b - ν - N := hab
        omega),
        ← Set.ncard_eq_toFinset_card _ hTV, hVc]
    · rw [Finset.card_image_of_injective _ Nat.cast_injective, ← Set.ncard_eq_toFinset_card _ hTW, hWc]
    · intro z hz
      obtain ⟨_, ha', _, hb', rfl⟩ := Finset.mem_add.1 hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ha'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hb'
      convert key a (hTV.mem_toFinset.1 ha) b (hTW.mem_toFinset.1 hb) using 1
      ring
  · rintro ⟨A, B, hA, hB, hAB⟩
    let a := A.orderEmbOfFin hA
    let b := B.orderEmbOfFin hB
    refine ⟨fun i => u ^ a i, fun j => u ^ b j, linearIndependent_zpow hT _ a.injective,
      linearIndependent_zpow hT _ b.injective, fun i j => ?_⟩
    apply Submodule.subset_span
    refine ⟨a i + b j, hAB (Finset.add_mem_add (A.orderEmbOfFin_mem hA i)
      (B.orderEmbOfFin_mem hB j)), ?_⟩
    simp only [zpow_add₀ hu0]
