-- Prove2me | solution 1 for Formalism.L2.Pj.LieAlg.eig_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:05.202724+00:00
-- url     : https://prove2.me/submissions/6f08e82d-0f0b-4974-a344-b720e8f2dc0b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
import Theorems.Thm_Formalism_L2_Pj_LieAlg_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace Formalism.L2.Pj.LieAlg
theorem _root_.solution {n m : ℕ} {ι : Type} (L : ι → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : ι → V)
    (M : ι → (Fin n → K) →ₗ[K] (Fin n → K))
    (hM : ∀ a c, M a (fun j => algebraMap V K (c j)) = fun j => algebraMap V K (L a c j))
    (v : Fin m → (Fin n → K)) (hv : ∀ a i, M a (v i) = algebraMap V K (χ a) • v i)
    (hb : ∀ w, (∀ a, M a w = algebraMap V K (χ a) • w) → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) :
    ∃ b : Fin m → (Fin n → V), (∀ a i, L a (b i) = χ a • b i) ∧
      (∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ i, r i • b i) ∧
      ∀ i, ∃ cf : Fin m → K, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧
        (fun j => algebraMap V K (b i j)) = ∑ j, cf j • v j := by
  classical
  let emb : (Fin n → V) → (Fin n → K) := fun c j => algebraMap V K (c j)
  have embinj : Function.Injective emb := fun c c' h =>
    funext fun j => IsFractionRing.injective V K (congrFun h j)
  have embadd : ∀ c c', emb (c + c') = emb c + emb c' := fun c c' => funext fun j => by simp [emb]
  have embsmul : ∀ (r : V) c, emb (r • c) = algebraMap V K r • emb c := fun r c =>
    funext fun j => by simp [emb]
  have embM : ∀ a c, M a (emb c) = emb (L a c) := fun a c => hM a c
  let E : Submodule V (Fin n → V) :=
    { carrier := {c | ∀ a, L a c = χ a • c}
      add_mem' := fun {c c'} hc hc' a => by
        simp only [Set.mem_setOf_eq] at hc hc' ⊢
        rw [map_add, hc a, hc' a, smul_add]
      zero_mem' := fun a => by simp
      smul_mem' := fun r c hc a => by
        simp only [Set.mem_setOf_eq] at hc ⊢
        rw [map_smul, hc a, smul_comm] }
  have memE : ∀ c, c ∈ E ↔ ∀ a, L a c = χ a • c := fun c => Iff.rfl
  have eigK : ∀ c ∈ E, ∀ a, M a (emb c) = algebraMap V K (χ a) • emb c := fun c hc a => by
    rw [embM, (memE c).1 hc a, embsmul]
  have hco : ∀ c : E, ∃! cf : Fin m → K, emb c = ∑ i, cf i • v i := fun c => hb _ (eigK c c.2)
  choose g spec hgu using hco
  let f : E →ₗ[V] (Fin m → K) :=
    { toFun := g
      map_add' := fun c c' => (hgu (c + c') _ (by
        rw [Submodule.coe_add, embadd, spec c, spec c', ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, add_smul])).symm
      map_smul' := fun r c => (hgu (r • c) _ (by
        rw [Submodule.coe_smul, embsmul, spec c, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [RingHom.id_apply, Pi.smul_apply, smul_smul]
        congr 1
        exact (Algebra.smul_def _ _).symm)).symm }
  have fspec : ∀ c : E, emb c = ∑ i, f c i • v i := spec
  have finj : Function.Injective f := fun x y h => Subtype.ext (embinj (by rw [fspec x, fspec y, h]))
  have hfg : (LinearMap.range f).FG := by
    rw [LinearMap.range_eq_map]
    exact (IsNoetherian.noetherian (⊤ : Submodule V E)).map f
  have hne : ∀ i : Fin m, ∃ α ∈ LinearMap.range f, (∀ j, i < j → α j = 0) ∧ α i ≠ 0 := by
    intro i
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors V) (Finset.univ) (v i)
    choose c hc using fun j => hd j (Finset.mem_univ j)
    have hcv : emb c = algebraMap V K (d : V) • v i := by
      funext j
      show algebraMap V K (c j) = _
      rw [hc j, Algebra.smul_def, Pi.smul_apply, smul_eq_mul]
    have hcE : c ∈ E := fun a => embinj (by
      rw [← embM, hcv, map_smul, hv, embsmul, hcv, smul_comm])
    have hfc : f ⟨c, hcE⟩ = Pi.single i (algebraMap V K (d : V)) := (hgu ⟨c, hcE⟩ _ (by
      show emb c = _
      rw [hcv, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul]) (by simp),
        Pi.single_eq_same])).symm
    refine ⟨f ⟨c, hcE⟩, ⟨⟨c, hcE⟩, rfl⟩, fun j hj => ?_, ?_⟩
    · rw [hfc, Pi.single_eq_of_ne (ne_of_gt hj)]
    · rw [hfc, Pi.single_eq_same]
      intro h0
      exact nonZeroDivisors.ne_zero d.2 (IsFractionRing.injective V K (by rw [h0, map_zero]))
  obtain ⟨β, hβΛ, hβz, hβd, hβu⟩ := herm m (LinearMap.range f) hfg hne
  choose e he using hβΛ
  refine ⟨fun i => (e i : Fin n → V), fun a i => (e i).2 a, ?_, ?_⟩
  · intro c hc
    have key : ∀ r' : Fin m → V, c = ∑ i, r' i • (e i : Fin n → V) ↔ f ⟨c, hc⟩ = ∑ i, r' i • β i := by
      intro r'
      have hsum : ((∑ i, r' i • e i : E) : Fin n → V) = ∑ i, r' i • (e i : Fin n → V) := by simp
      have hf : f (∑ i, r' i • e i) = ∑ i, r' i • β i := by simp [map_sum, map_smul, he]
      constructor
      · intro h
        rw [← hf]
        congr 1
        exact Subtype.ext (by rw [hsum]; exact h)
      · intro h
        rw [← hf] at h
        have h' := congrArg Subtype.val (finj h)
        rw [hsum] at h'
        exact h'
    obtain ⟨r, hr, hru⟩ := hβu (f ⟨c, hc⟩) ⟨⟨c, hc⟩, rfl⟩
    exact ⟨r, (key r).2 hr, fun r' h => hru r' ((key r').1 h)⟩
  · intro i
    refine ⟨β i, hβd i, hβz i, ?_⟩
    have h9 := fspec (e i)
    rw [he i] at h9
    exact h9
end Formalism.L2.Pj.LieAlg
