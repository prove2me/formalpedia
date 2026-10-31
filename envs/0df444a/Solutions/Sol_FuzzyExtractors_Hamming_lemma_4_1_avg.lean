-- Prove2me | solution 1 for FuzzyExtractors.Hamming.lemma_4_1_avg
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T01:24:24.685472+00:00
-- url     : https://prove2.me/submissions/0bb5c2f0-ef23-419e-ab58-85adf9d87b5f

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal Classical
open FuzzyExtractors.Hamming

namespace Lemma41AvgProof

variable {A B : Type*}

theorem map_equiv_apply (P : PMF A) (e : A ≃ B) (b : B) :
    (P.map e) b = P (e.symm b) := by
  rw [PMF.map_apply]
  simpa only [Equiv.eq_symm_apply, eq_comm, if_true] using
    (tsum_eq_single (e.symm b) (fun a ha => if_neg ha) :
      (∑' a, if a = e.symm b then P a else 0) =
        if e.symm b = e.symm b then P (e.symm b) else 0)

theorem statDist_map_equiv (P Q : PMF A) (e : A ≃ B) :
    statDist (P.map e) (Q.map e) = statDist P Q := by
  unfold statDist
  simp only [map_equiv_apply]
  congr 1
  exact e.symm.tsum_eq (fun v => |(P v).toReal - (Q v).toReal|)

def helperReorder {B X S I : Type} : (B × X × (S × I)) ≃ (B × (S × X) × I) where
  toFun a := (a.1, (a.2.2.1, a.2.1), a.2.2.2)
  invFun a := (a.1, a.2.1.2, (a.2.1.1, a.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem composition_correct {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (dis : M → M → ℕ) (t : ℕ) (SS : M → PMF S) (Rec : M → S → PMF M)
    (Ext : M → X → (Fin ℓ → Bool)) (hcorrect : SketchCorrect dis t SS Rec) :
    ExtractorCorrect dis t (sketchExtGen SS Ext) (sketchExtRep Rec Ext) := by
  intro w w' hw rp hrp
  obtain ⟨s, hs, h⟩ := (PMF.mem_support_bind_iff _ _ _).1 hrp
  obtain ⟨x, _, hxeq⟩ := (PMF.mem_support_map_iff _ _ _).1 h
  subst rp
  simp only [sketchExtRep, hcorrect w w' hw s hs, PMF.pure_map]

theorem composition_law {M S X I : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (P : PMF (M × I)) :
    (P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2)) =
      (extractLawAux Ext (withSketchAux SS P)).map helperReorder := by
  simp only [sketchExtGen, extractLawAux, withSketchAux, PMF.map_bind, PMF.bind_map,
    PMF.bind_bind, PMF.map_comp, Function.comp_def, helperReorder, Equiv.coe_fn_mk]

theorem composition_distance {M S X I : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (SS : M → PMF S) (Ext : M → X → (Fin ℓ → Bool)) (P : PMF (M × I)) :
    statDist
      (P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2))
      ((P.bind fun p => (sketchExtGen SS Ext p.1).map fun rp => (rp.1, rp.2, p.2)).bind
        fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) =
    statDist (extractLawAux Ext (withSketchAux SS P))
      ((extractLawAux Ext (withSketchAux SS P)).bind
        fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) := by
  rw [composition_law]
  have h (Q : PMF ((Fin ℓ → Bool) × X × (S × I))) :
      (Q.map helperReorder).bind (fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)) =
      (Q.bind fun a => (uniformBits ℓ).map fun u => (u, a.2.1, a.2.2)).map helperReorder := by
    simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def,
      helperReorder, Equiv.coe_fn_mk]
  rw [h, statDist_map_equiv]

end Lemma41AvgProof

theorem solution {M S X : Type} [Fintype X] [Nonempty X] {ℓ : ℕ}
    (dis : M → M → ℕ) (m m' ε : ℝ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hSS : IsAvgSecureSketch dis m m' t SS Rec)
    (Ext : M → X → (Fin ℓ → Bool)) (hExt : IsAvgStrongExtractor m' ε Ext) :
    IsAvgFuzzyExtractor dis m ℓ t ε (sketchExtGen SS Ext) (sketchExtRep Rec Ext) := by
  refine ⟨Lemma41AvgProof.composition_correct dis t SS Rec Ext hSS.1, ?_⟩
  intro ι WI hm
  rw [Lemma41AvgProof.composition_distance]
  exact hExt (S × ι) (withSketchAux SS WI) (hSS.2 ι WI hm)
