-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.shear_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:59.487178+00:00
-- url     : https://prove2.me/submissions/b5f5a75a-c5d0-4f7c-9df3-2298ec69ea0e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_ShearMp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
namespace Formalism.L2.SG.NGCut.SplitEmbedding
private theorem measurePreserving_pi_shear_of_indep {P : Type} [Fintype P]
    {α : P → Type} [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (S : P → Prop) [DecidablePred S] (d : ∀ p, (∀ q, α q) → α p) (hd : ∀ p, Measurable (d p))
    (hind : ∀ p, S p → ∀ x x' : ∀ q, α q, (∀ q, ¬ S q → x q = x' q) → d p x = d p x') :
    MeasurePreserving (fun g q => if S q then g q + d q g else g q)
      (Measure.pi μ) (Measure.pi μ) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd μ (fun q => ¬ S q)
  set e := MeasurableEquiv.piEquivPiSubtypeProd α (fun q => ¬ S q) with he
  have hfwd : ∀ g : ∀ q, α q, e g = (fun i : {q // ¬ S q} => g i.1, fun i : {q // ¬ ¬ S q} => g i.1) :=
    fun _ => rfl
  have hsymm : ∀ (x : ∀ i : {q // ¬ S q}, α i) (y : ∀ i : {q // ¬ ¬ S q}, α i) (q : P),
      e.symm (x, y) q = if h : ¬ S q then x ⟨q, h⟩ else y ⟨q, h⟩ := fun _ _ _ => rfl
  let v : (∀ i : {q // ¬ S q}, α i) → ∀ i : {q // ¬ ¬ S q}, α i :=
    fun x i => d i.1 (e.symm (x, 0))
  have hvdef : ∀ x i, v x i = d i.1 (e.symm (x, 0)) := fun _ _ => rfl
  have hv : Measurable v := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact (hd i.1).comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  have hgm : Measurable (Function.uncurry fun (x : ∀ i : {q // ¬ S q}, α i)
      (y : ∀ i : {q // ¬ ¬ S q}, α i) => fun i => y i + v x i) := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact Measurable.add ((measurable_pi_apply i).comp measurable_snd)
      ((measurable_pi_apply i).comp (hv.comp measurable_fst))
  have hgae : ∀ᵐ x ∂(Measure.pi fun i : {q // ¬ S q} => μ i),
      Measure.map (fun y : ∀ i : {q // ¬ ¬ S q}, α i => fun i => y i + v x i)
        (Measure.pi fun i : {q // ¬ ¬ S q} => μ i) = Measure.pi fun i : {q // ¬ ¬ S q} => μ i :=
    ae_of_all _ fun x =>
      (measurePreserving_pi (hf := fun i => measurePreserving_add_right (μ i.1) (v x i))).map_eq
  have h2 := MeasurePreserving.skew_product (MeasurePreserving.id _) hgm hgae
  have h3 := MeasurePreserving.symm _ h1
  have key : (fun g q => if S q then g q + d q g else g q) =
      (⇑e.symm ∘ (fun z : (∀ i : {q // ¬ S q}, α i) × (∀ i : {q // ¬ ¬ S q}, α i) =>
        (id z.1, fun i => z.2 i + v z.1 i))) ∘ ⇑e := by
    funext g q
    by_cases hq : S q
    · have hd' : d q (e.symm ((fun i : {q // ¬ S q} => g i.1), 0)) = d q g :=
        hind q hq _ _ (fun q' hq' => by simp [hsymm, hq'])
      simp [hfwd, hsymm, hq, hvdef, hd']
    · simp [hfwd, hsymm, hq]
  rw [key]
  exact (h3.comp h2).comp h1
end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution : ∀ (n : ℕ) (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = n →
    ∀ (α : P → Type) [∀ p, AddGroup (α p)] [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
      (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
      (h : P → ℕ) (c : ∀ p, (∀ q, α q) → α p), (∀ p, Measurable (c p)) →
      (∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → c p x = c p x') →
      MeasurePreserving (fun g p => g p + c p g) (Measure.pi μ) (Measure.pi μ) := by
  intro n P _ _ _ α _ _ _ μ _ _ h c hc hdep
  have hstep : ∀ k : ℕ, MeasurePreserving (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p)
      (Measure.pi μ) (Measure.pi μ) := by
    intro k
    induction k with
    | zero =>
      have h0 : (fun (g : ∀ q, α q) p => if h p < 0 then g p + c p g else g p) = id := by
        funext g p
        simp
      rw [h0]
      exact MeasurePreserving.id _
    | succ k ih =>
      have hL := measurePreserving_pi_shear_of_indep μ (fun q => h q = k) c hc
        (fun p hp x x' hx => hdep p x x' (fun q hq => hx q (by omega)))
      have heq : (fun (g : ∀ q, α q) p => if h p < k + 1 then g p + c p g else g p) =
          (fun (g : ∀ q, α q) p => if h p < k then g p + c p g else g p) ∘
            (fun (g : ∀ q, α q) q => if h q = k then g q + c q g else g q) := by
        funext g p
        simp only [Function.comp_apply]
        rcases lt_trichotomy (h p) k with hp | hp | hp
        · have hc' : c p (fun q => if h q = k then g q + c q g else g q) = c p g :=
            hdep p _ _ (fun q hq => by simp [show h q ≠ k by omega])
          simp [hp, show h p < k + 1 by omega, show h p ≠ k by omega, hc']
        · simp [hp]
        · simp [show ¬ h p < k + 1 by omega, show ¬ h p < k by omega, show h p ≠ k by omega]
      rw [heq]
      exact ih.comp hL
  have hfull : (fun (g : ∀ q, α q) p => g p + c p g) =
      (fun (g : ∀ q, α q) p => if h p < Finset.univ.sup h + 1 then g p + c p g else g p) := by
    funext g p
    have hle : h p ≤ Finset.univ.sup h := Finset.le_sup (Finset.mem_univ p)
    simp [show h p < Finset.univ.sup h + 1 by omega]
  rw [hfull]
  exact hstep _
end Formalism.L2.SG.NGCut.SplitEmbedding
