-- Prove2me | solution 1 for Formalism.UG.P.UG_stabilizer_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:23:58.231796+00:00
-- url     : https://prove2.me/submissions/558c6242-b59d-44a7-9741-ff2e8b5bef94

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Theorems.Thm_Formalism_UG_P_sf_den
import Theorems.Thm_Formalism_UG_P_sf_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.StabFinite := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan
  classical
  obtain ⟨dJ, hdJ0, -, hdJ⟩ := sf_den (fun p : n × n => J p.1 p.2)
  obtain ⟨S, hS⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨dL, hdL0, -, hdL⟩ := sf_den (fun p : S × n => (p.1 : n → E) p.2)
  have hΛint : ∀ v ∈ Λ, ∀ k, IsIntegral ℤ (dL * v k) := by
    intro v hv
    rw [← hS] at hv
    induction hv using Submodule.span_induction with
    | mem x hx => intro k; exact hdL (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (r • x) k = (algebraMap (𝓞 E) E r) * x k := by
        rw [Pi.smul_apply, Algebra.smul_def]
      rw [this, mul_left_comm]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hcol : ∀ j : n, ∃ c : E, c ≠ 0 ∧ c • (Pi.single j 1 : n → E) ∈ Λ := by
    intro j
    have hm : (Pi.single j 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; trivial
    obtain ⟨m, f, gg, hsum⟩ := Submodule.mem_span_set'.mp hm
    obtain ⟨d, hd0, -, hd⟩ := sf_den f
    refine ⟨d, hd0, ?_⟩
    rw [← hsum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun l _ => ?_)
    obtain ⟨r, hr⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hd l)
    have : d • (f l • (gg l : n → E)) = r • (gg l : n → E) := by
      rw [smul_smul, ← hr, algebraMap_smul]
    rw [this]
    exact Λ.smul_mem r (gg l).2
  choose c hc0 hcΛ using hcol
  let β : (E →+* ℂ) × n × n → ℝ := fun z =>
    ‖z.1 (dJ * dL * c z.2.2)‖ * (‖z.1 (J z.2.1 z.2.1)‖ + ‖z.1 (J z.2.2 z.2.2)‖)
  obtain ⟨B, hB⟩ := (Set.finite_range β).bddAbove
  set T : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} with hT
  have hTfin : T.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  have hmem : ∀ g ∈ level (σ : E →+* E) J Λ, ∀ i j,
      dJ * dL * c j * ((J * (g : Matrix n n E)) i j) ∈ T := by
    intro g hg i j
    have hU : cT (σ : E →+* E) (g : Matrix n n E) * J * (g : Matrix n n E) = J := hg.1
    have hstab : ∀ x : n → E, x ∈ Λ ↔ (g : Matrix n n E) *ᵥ x ∈ Λ := hg.2
    have hgc : (g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E)) ∈ Λ := (hstab _).mp (hcΛ j)
    have hcoord : ∀ k, ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k =
        c j * (g : Matrix n n E) k j := by
      intro k; simp [Matrix.mulVec_smul]
    refine ⟨?_, fun φ => ?_⟩
    · have : dJ * dL * c j * ((J * (g : Matrix n n E)) i j) =
          ∑ k, (dJ * J i k) * (dL * ((g : Matrix n n E) *ᵥ (c j • (Pi.single j 1 : n → E))) k) := by
        simp only [hcoord, Matrix.mul_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_); ring
      rw [this]
      exact IsIntegral.sum _ (fun k _ => (hdJ (i, k)).mul (hΛint _ hgc k))
    · rw [map_mul, norm_mul]
      calc ‖φ (dJ * dL * c j)‖ * ‖φ ((J * (g : Matrix n n E)) i j)‖
          ≤ ‖φ (dJ * dL * c j)‖ * (‖φ (J i i)‖ + ‖φ (J j j)‖) :=
            mul_le_mul_of_nonneg_left (sf_bound σ J φ (hτ φ) hH hdef.2 _ hU i j) (norm_nonneg _)
        _ = β (φ, i, j) := rfl
        _ ≤ B := hB ⟨(φ, i, j), rfl⟩
  have : Finite T := hTfin.to_subtype
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr hdet
  refine Finite.of_injective
    (fun g : level (σ : E →+* E) J Λ => fun i j => (⟨_, hmem g.1 g.2 i j⟩ : T)) ?_
  intro g g' hgg
  have h1 : J * (g.1 : Matrix n n E) = J * (g'.1 : Matrix n n E) := by
    ext i j
    have := congr_arg Subtype.val (congr_fun (congr_fun hgg i) j)
    exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hdJ0 hdL0) (hc0 j)) this
  exact Subtype.ext (Units.ext (hJu.mul_left_cancel h1))
end Formalism.UG.P
