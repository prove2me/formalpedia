-- Prove2me | solution 1 for DeletionHash.MixedEdit.independent_differences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:59:56.896803+00:00
-- url     : https://prove2.me/submissions/b90635fe-6451-47dc-97e8-3de46d95f7e5

import Mathlib
import Definitions.Def_DeletionHash_MixedEdit_Labels
namespace DeletionGeneralization.HashUniform
open DeletionHash.MixedEdit
universe u v
variable {ι : Type u} [Fintype ι] {R r : ℕ}

noncomputable def evaluation (v : Fin R → (ι → ZMod 2)) :
    (ι → Label r) →ₗ[ZMod 2] (Fin R → Label r) :=
  LinearMap.pi (fun i => ∑ g, v i g • LinearMap.proj g)

theorem evaluation_apply (v : Fin R → (ι → ZMod 2)) (ξ : ι → Label r) (i : Fin R) :
    evaluation v ξ i = ∑ g, v i g • ξ g := by
  simp [evaluation]

theorem evaluation_surjective (v : Fin R → (ι → ZMod 2))
    (hv : LinearIndependent (ZMod 2) v) : Function.Surjective (evaluation (r := r) v) := by
  classical
  let f := Fintype.linearCombination (ZMod 2) v
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  intro a
  let h : (ι → ZMod 2) →ₗ[ZMod 2] Label r :=
    (Fintype.linearCombination (ZMod 2) a).comp g
  have hvh : ∀ i, h (v i) = a i := by
    intro i
    have he := LinearMap.congr_fun hg (Pi.single i 1)
    have hi : f (Pi.single i 1) = v i := by
      simp [f, Fintype.linearCombination_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hi] at he
    simp [h, he, Fintype.linearCombination_apply]
  refine ⟨fun j => h (Pi.single j 1), ?_⟩
  funext i
  rw [evaluation_apply, ← hvh i]
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply, mul_ite]

theorem uniform_fiber {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (hf : Function.Surjective f) (a : W) :
    uniformProbability (fun x => f x = a) = 1 / (Fintype.card W : ℝ) := by
  classical
  have heq : ∀ y : W, Fintype.card {x : V // f x = y} = Fintype.card {x : V // f x = a} := by
    intro y
    simpa only [Fintype.card_subtype] using
      (AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf a))
  have hc : Fintype.card V = Fintype.card W * Fintype.card {x : V // f x = a} := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simpa only [Fintype.card_sigma, heq, Finset.sum_const, Finset.card_univ, smul_eq_mul] using h.symm
  have hn : 0 < Fintype.card {x : V // f x = a} := by
    obtain ⟨x,hx⟩ := hf a
    exact Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩
  unfold uniformProbability
  rw [Nat.card_eq_fintype_card, hc, Nat.cast_mul]
  have hne : (Fintype.card {x : V // f x = a} : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp


theorem joint {α : Type u} [Fintype α] [DecidableEq α] {L r R : ℕ}
    (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) (a : Fin R → Label r) :
    uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      1 / ((2 : ℝ)^r)^R := by
  classical
  have he : (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      (fun ξ => evaluation (fun i => parity (w i)) ξ = a) := by
    funext ξ
    simp only [funext_iff, evaluation_apply, DeletionHash.MixedEdit.hash]
  rw [he]
  have h := uniform_fiber (evaluation (r := r) (fun i => parity (w i))).toAddMonoidHom
    (evaluation_surjective _ hw) a
  simpa [Label, Fintype.card_fun, ZMod.card] using h

theorem single {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (v : Spectrum α L) (hv : parity v ≠ 0) :
    uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2 : ℝ)^r := by
  have hi : LinearIndependent (ZMod 2) (fun _ : Fin 1 => parity v) := by
    rw [linearIndependent_unique_iff]
    exact hv
  simpa using joint (r := r) (fun _ : Fin 1 => v) hi (fun _ => 0)

end DeletionGeneralization.HashUniform
open DeletionHash.MixedEdit

universe u

/-- Lemma 3.2: full joint uniform law, rule survival, and the single-vector law. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (L r R k t b : ℕ) (hr : 1 ≤ r) (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) :
    (∀ a : Fin R → Label r,
      uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
        1 / ((2 : ℝ)^r)^R) ∧
    ((∀ i, w i ∈ Catalogue k L t b) →
      uniformProbability (fun ξ : HashSample α L r => ∀ i, Survives k t b ξ (w i)) =
        1 / ((2 : ℝ)^r)^R) ∧
    (∀ v : Spectrum α L, parity v ≠ 0 →
      uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2 : ℝ)^r) := by
  refine ⟨DeletionGeneralization.HashUniform.joint w hw, ?_,
    fun v hv => DeletionGeneralization.HashUniform.single v hv⟩
  intro hcat
  simpa only [Survives, hcat, true_and] using
    DeletionGeneralization.HashUniform.joint (r := r) w hw (fun _ => 0)



#print axioms solution
