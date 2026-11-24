-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenA.gen_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:32.896482+00:00
-- url     : https://prove2.me/submissions/c34302f7-aede-4d35-9759-ef8f099cccd7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenA_coprS_le
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenA_primes_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
namespace Formalism.MainNotions.BridgeLevelGenA
theorem _root_.solution (g : R) (hg : g ≠ 0) {n : ℕ} (L : Submodule R (Fin n → K)) (hL : L.FG) :
    ∃ (m : ℕ) (ℓ : Fin m → (Fin n → K)), m ≤ n ∧ (∀ j, ℓ j ∈ L) ∧
      ∀ x ∈ L, ∃ (a : Fin m → R) (w : Fin n → K), w ∈ L ∧ x = ∑ j, a j • ℓ j + g • w := by
  classical
  set S := coprS g with hSdef
  let A := Localization.subalgebra.ofField K S (coprS_le g)
  have : IsDedekindDomain A := IsLocalization.isDedekindDomain R (coprS_le g) A
  have : IsFractionRing A K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S A K
  have : IsPrincipalIdealRing A := by
    refine IsPrincipalIdealRing.of_finite_primes ?_
    refine ((primes_finite g hg).preimage (IsLocalization.orderEmbedding S A).injective.injOn).subset ?_
    intro J hJ
    exact (IsLocalization.isPrime_iff_isPrime_disjoint S A J).1 hJ
  let M : Submodule A (Fin n → K) := Submodule.span A (L : Set (Fin n → K))
  have : Module.Finite A M := by
    obtain ⟨s, hs⟩ := hL
    have e : M = Submodule.span A (s : Set (Fin n → K)) := by
      show Submodule.span A (L : Set (Fin n → K)) = _
      rw [← hs, Submodule.span_span_of_tower]
    rw [Module.Finite.iff_fg, e]
    exact ⟨s, rfl⟩
  have : Module.IsTorsionFree A M := by
    refine ⟨fun r hr x y hxy => Subtype.ext ?_⟩
    have hr0 : (r : K) ≠ 0 := by
      intro h
      exact hr.ne_zero (Subtype.ext (by simpa using h))
    have h := congrArg (fun z : M => (z : Fin n → K)) hxy
    simp only [Submodule.coe_smul, Subalgebra.smul_def] at h
    exact smul_right_injective _ hr0 h
  have : Module.Free A M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex A M
  let b : Module.Basis ι A M := Module.Free.chooseBasis A M

  have hcard : Fintype.card ι ≤ n := by
    have hli : LinearIndependent A (fun i => (b i : Fin n → K)) :=
      b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    have hK := (LinearIndependent.iff_fractionRing A K).1 hli
    simpa using hK.fintype_card_le_finrank

  have hden : ∀ v ∈ M, ∃ s ∈ S, algebraMap R K s • v ∈ L := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, S.one_mem, by simpa using hx⟩
    | zero => exact ⟨1, S.one_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨s * t, S.mul_mem hs ht, ?_⟩
      have e : algebraMap R K (s * t) • (x + y) = t • (algebraMap R K s • x) + s • (algebraMap R K t • y) := by
        rw [smul_add, ← algebraMap_smul K t (algebraMap R K s • x), ← algebraMap_smul K s (algebraMap R K t • y),
          smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm t s]
      rw [e]
      exact L.add_mem (L.smul_mem t hsx) (L.smul_mem s hty)
    | smul a x _ hx =>
      obtain ⟨s, hs, hsx⟩ := hx
      obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.mk'_surjective S a
      refine ⟨t * s, S.mul_mem t.2 hs, ?_⟩
      have ha : (a : K) * algebraMap R K t = algebraMap R K r := by
        rw [← hrt]
        have h2 : ((IsLocalization.mk' A r t * algebraMap R A t : A) : K) = ((algebraMap R A r : A) : K) :=
          congrArg Subtype.val (IsLocalization.mk'_spec A r t)
        rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap] at h2
        exact h2
      have e : algebraMap R K (t * s) • (a • x) = r • (algebraMap R K s • x) := by
        rw [Subalgebra.smul_def, smul_smul, ← algebraMap_smul K r, smul_smul, map_mul, ← ha]
        congr 1; ring
      rw [e]
      exact L.smul_mem r hsx
  choose sd hsd hsdL using fun i => hden (b i : Fin n → K) (b i).2
  set s : R := ∏ i, sd i with hs
  have hsS : s ∈ S := S.prod_mem fun i _ => hsd i
  let ℓ : ι → (Fin n → K) := fun i => algebraMap R K s • (b i : Fin n → K)
  have hℓ : ∀ i, ℓ i ∈ L := by
    intro i
    obtain ⟨c, hc⟩ : sd i ∣ s := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have e : ℓ i = c • (algebraMap R K (sd i) • (b i : Fin n → K)) := by
      show algebraMap R K s • (b i : Fin n → K) = _
      rw [hc, ← algebraMap_smul K c, smul_smul, ← map_mul, mul_comm c (sd i)]
    rw [e]
    exact L.smul_mem c (hsdL i)

  have hx : ∀ x ∈ L, ∃ (a : ι → R) (w : Fin n → K), w ∈ L ∧ x = ∑ i, a i • ℓ i + g • w := by
    intro x hxL
    have hxM : x ∈ M := Submodule.subset_span hxL
    set c := b.repr ⟨x, hxM⟩ with hc
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples S Finset.univ (fun i => c i)
    choose r hr using fun i => ht i (Finset.mem_univ i)
    have hsum : x = ∑ i, (c i : K) • (b i : Fin n → K) := by
      have := congrArg (fun z : M => (z : Fin n → K)) (b.sum_repr ⟨x, hxM⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def] at this
      rw [← hc] at this
      exact this.symm
    have hri : ∀ i, algebraMap R K (r i) = algebraMap R K (t : R) * (c i : K) := by
      intro i
      have h2 : ((algebraMap R A (r i) : A) : K) = (((t : R) • c i : A) : K) := congrArg Subtype.val (hr i)
      rw [Subalgebra.coe_algebraMap, Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap] at h2
      exact h2
    set u : R := (t : R) * s with hu_def
    have hux : algebraMap R K u • x = ∑ i, r i • ℓ i := by
      rw [hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = r i • (algebraMap R K s • (b i : Fin n → K))
      rw [← algebraMap_smul K (r i), smul_smul, smul_smul, hri, hu_def, map_mul]
      congr 1; ring
    have hu : u ∈ S := S.mul_mem t.2 hsS
    obtain ⟨α, β, hαβ⟩ := hu.1
    refine ⟨fun i => α * r i, β • x, L.smul_mem β hxL, ?_⟩
    have h1 : algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β = 1 := by
      rw [← map_mul, ← map_mul, ← map_add, mul_comm g β, hαβ, map_one]
    calc x = (algebraMap R K α * algebraMap R K u + algebraMap R K g * algebraMap R K β) • x := by
          rw [h1, one_smul]
      _ = α • (algebraMap R K u • x) + g • (β • x) := by
          rw [add_smul, ← smul_smul, ← smul_smul, algebraMap_smul K α, algebraMap_smul K g, algebraMap_smul K β]
      _ = _ := by
          rw [hux, Finset.smul_sum]
          simp only [smul_smul]

  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => ℓ (e.symm j), hcard, fun j => hℓ _, fun x hxL => ?_⟩
  obtain ⟨a, w, hw, hxw⟩ := hx x hxL
  refine ⟨fun j => a (e.symm j), w, hw, ?_⟩
  rw [hxw]
  congr 1
  exact (Equiv.sum_comp e.symm (fun i => a i • ℓ i)).symm
end Formalism.MainNotions.BridgeLevelGenA
