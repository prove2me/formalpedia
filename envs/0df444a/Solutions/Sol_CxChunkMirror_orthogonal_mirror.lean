-- Prove2me | solution 1 for CxChunkMirror.orthogonal_mirror
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:17:05.358499+00:00
-- url     : https://prove2.me/submissions/ed72622a-8072-4602-a2bb-bf1793753872

import Definitions.Def_IntMul_Kappa_CxChunkMirror

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
The validity and rank formulas below use the public round-six chunk language.
The append, dimension and nondegeneracy helpers follow xuanji’s accepted
round-six solution, Prove2Me submission 534cb506-9a9f-4445-8a59-416047960d9d.
-/
namespace CxMirrorProof

open IntMul.Kappa.R6.Cx NetComplexP8 NetComplexLabels NetLabels Matrix Module CxChunkMirror
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {R : Type} [Fintype R] [DecidableEq R] {m n : ℕ}

lemma progValid_append :
    ∀ (a b : List (GChunk R m)) (lab : R → Lab m),
      ProgValid (a ++ b) lab ↔ ProgValid a lab ∧ ProgValid b (progLab a lab) := by
  intro a
  induction a with
  | nil => intro b lab; simp [ProgValid, progLab]
  | cons C a ih =>
    intro b lab
    simp only [List.cons_append, ProgValid, progLab, ih]
    tauto

lemma progLab_append (a b : List (GChunk R m)) (lab : R → Lab m) :
    progLab (a ++ b) lab = progLab b (progLab a lab) := by
  induction a generalizing lab with
  | nil => rfl
  | cons C a ih => simp [progLab, ih]

lemma det_one_ne {n : ℕ} : (1 : Matrix (Fin n) (Fin n) (ZMod 2)).det ≠ 0 := by
  rw [det_one]; exact one_ne_zero

lemma finrank_compl {n : ℕ} {U : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (hU : NondegOn (1 : Matrix (Fin n) (Fin n) (ZMod 2)) U) :
    finrank (ZMod 2) U + finrank (ZMod 2) (orth 1 U) = n := by
  have := Submodule.finrank_add_eq_of_isCompl (isCompl_orth one_isSymm hU)
  rwa [Module.finrank_fin_fun] at this

theorem Fd_eq_natAbs {n : ℕ} {V U : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : EdgeOK V U) :
    Fd V U = Int.natAbs ((finrank (ZMod 2) V : ℤ) - finrank (ZMod 2) U) := by
  rcases h with h | h
  · have := Fd_up h
    rw [← this]; rfl
  · have := Fd_down h
    rw [← neg_sub, Int.natAbs_neg, ← this]; rfl

lemma nondeg_of_edge_left {n : ℕ} {V U : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : EdgeOK V U) :
    NondegOn (1 : Matrix (Fin n) (Fin n) (ZMod 2)) V := by
  rcases h with h | h
  · exact h.2.1
  · exact h.1

lemma nondeg_of_edge_right {n : ℕ} {V U : Submodule (ZMod 2) (Fin n → ZMod 2)} (h : EdgeOK V U) :
    NondegOn (1 : Matrix (Fin n) (Fin n) (ZMod 2)) U := by
  rcases h with h | h
  · exact h.1
  · exact h.2.1

private theorem inverse_dst (o : GOp R) : (inverseSignedGate o).dst = o.dst := by
  unfold inverseSignedGate
  split <;> rfl

private theorem inverse_src (o : GOp R) : (inverseSignedGate o).src = o.src := by
  unfold inverseSignedGate
  split <;> rfl

private theorem restoreLabel (f : Lab m → Lab n) (lab : R → Lab m) (r : R) (v u : Lab m)
    (old : lab r = u) :
    Function.update (f ∘ Function.update lab r v) r (f u) = f ∘ lab := by
  funext a
  by_cases ha : a = r
  · subst a
    simp [old]
  · simp [Function.comp_apply, Function.update_of_ne ha]

/-- Reflection of all source-edge proofs suffices to return the entire role-label map. -/
theorem backwardMoves_sound (f : Lab m → Lab n)
    (edge : ∀ {v u}, EdgeOK v u → EdgeOK (f u) (f v)) (v : Lab m)
    (ps : List (R × Lab m)) (lab : R → Lab m) (valid : MvValid v ps lab) :
    ProgValid (backwardMoves f v ps) (f ∘ mvLab v ps lab) ∧
    progLab (backwardMoves f v ps) (f ∘ mvLab v ps lab) = f ∘ lab := by
  induction ps generalizing lab with
  | nil => exact ⟨trivial, rfl⟩
  | cons p ps ih =>
    obtain ⟨old, good, tail⟩ := valid
    let l := Function.update lab p.1 v
    obtain ⟨ok, finish⟩ := ih l tail
    change ProgValid (backwardMoves f v ps ++ [backwardMove f v p]) (f ∘ mvLab v ps l) ∧
      progLab (backwardMoves f v ps ++ [backwardMove f v p]) (f ∘ mvLab v ps l) = f ∘ lab
    rw [progValid_append, progLab_append, finish]
    refine ⟨⟨ok, ?_⟩, ?_⟩
    · simp [backwardMove, ProgValid, GChunk.Valid, MvValid, l, edge good]
    · exact restoreLabel f lab p.1 v p.2 old

theorem backwardChunk_sound (f : Lab m → Lab n)
    (edge : ∀ {v u}, EdgeOK v u → EdgeOK (f u) (f v)) (c : GChunk R m)
    (lab : R → Lab m) (valid : c.Valid lab) :
    ProgValid (backwardChunk f c) (f ∘ mvLab c.V c.mv lab) ∧
    progLab (backwardChunk f c) (f ∘ mvLab c.V c.mv lab) = f ∘ lab := by
  have hm := backwardMoves_sound f edge c.V c.mv lab valid.1
  refine ⟨⟨⟨trivial, ?_⟩, hm.1⟩, hm.2⟩
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
  have g := valid.2 a (List.mem_reverse.mp ha)
  simp only [mvLab, Function.comp_apply, inverse_dst, inverse_src, g.1, g.2, and_self]

/-- Any valid forward program gives a valid mirrored program on the mapped
end labels, and the latter finishes on the mapped starting labels. -/
theorem backwardProgram_sound (f : Lab m → Lab n)
    (edge : ∀ {v u}, EdgeOK v u → EdgeOK (f u) (f v))
    (cs : List (GChunk R m)) (lab : R → Lab m) (valid : ProgValid cs lab) :
    ProgValid (backwardProgram f cs) (f ∘ progLab cs lab) ∧
    progLab (backwardProgram f cs) (f ∘ progLab cs lab) = f ∘ lab := by
  induction cs generalizing lab with
  | nil => exact ⟨trivial, rfl⟩
  | cons c cs ih =>
    obtain ⟨hc, ht⟩ := valid
    have hs := backwardChunk_sound f edge c lab hc
    have tail := ih (mvLab c.V c.mv lab) ht
    have expand : backwardProgram f (c :: cs) = backwardProgram f cs ++ backwardChunk f c := by
      simp [backwardProgram]
    rw [expand, progValid_append, progLab_append]
    change (ProgValid _ _ ∧ ProgValid _ (progLab _ (f ∘ progLab cs (mvLab c.V c.mv lab)))) ∧
      progLab _ (progLab _ (f ∘ progLab cs (mvLab c.V c.mv lab))) = _
    rw [tail.2]
    exact ⟨⟨tail.1, hs.1⟩, hs.2⟩

omit [DecidableEq R] in
private theorem widths_append {k : ℕ} (a b : List (GChunk R k)) :
    progWidths (a ++ b) = progWidths a ++ progWidths b := List.flatMap_append ..

omit [DecidableEq R] in
private theorem mvWidths_cons (v : Lab m) (p : R × Lab m) (ps : List (R × Lab m)) :
    mvWidths v (p :: ps) = mvWidths v [p] ++ mvWidths v ps := by
  simp [mvWidths]

/-- A complementary move has the original charge. Paid charges appear in reverse order. -/
theorem backwardMoves_widths (f : Lab m → Lab n)
    (width : ∀ {v u}, EdgeOK v u → Fd (f u) (f v) = Fd v u) (v : Lab m)
    (ps : List (R × Lab m)) (lab : R → Lab m) (valid : MvValid v ps lab) :
    progWidths (backwardMoves f v ps) = (mvWidths v ps).reverse := by
  induction ps generalizing lab with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨_, good, ht⟩ := valid
    have one : progWidths [backwardMove f v p] = (mvWidths v [p]).reverse := by
      by_cases hz : Fd v p.2 = 0 <;> simp [progWidths, backwardMove, mvWidths, width good, hz]
    change progWidths (backwardMoves f v ps ++ [backwardMove f v p]) = _
    rw [widths_append, ih _ ht, one, mvWidths_cons v p ps, List.reverse_append]

theorem backwardProgram_widths (f : Lab m → Lab n)
    (width : ∀ {v u}, EdgeOK v u → Fd (f u) (f v) = Fd v u)
    (cs : List (GChunk R m)) (lab : R → Lab m) (valid : ProgValid cs lab) :
    progWidths (backwardProgram f cs) = (progWidths cs).reverse := by
  induction cs generalizing lab with
  | nil => rfl
  | cons c cs ih =>
    have expand : backwardProgram f (c :: cs) = backwardProgram f cs ++ backwardChunk f c := by
      simp [backwardProgram]
    have localWidths : progWidths (backwardChunk f c) = (mvWidths c.V c.mv).reverse :=
      backwardMoves_widths f width c.V c.mv lab valid.1.1
    rw [expand, widths_append, ih _ valid.2, localWidths]
    exact (List.reverse_append ..).symm

/-- The round-six proof of the increasing-edge complement lemma works at every dimension. -/
theorem up_orth {u v : Lab m} (h : Up u v) : Up (orth 1 v) (orth 1 u) := by
  obtain ⟨hu, hv, hle, hw⟩ := h
  refine ⟨nondeg_orth one_isSymm hv det_one_ne, nondeg_orth one_isSymm hu det_one_ne, ?_, ?_⟩
  · intro y hy
    rw [mem_orth_one] at hy ⊢
    exact fun x hx => hy x (hle hx)
  · rcases hw with rfl | ⟨w, hwv, hww, hwo⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨w, mem_orth_one.2 fun x hx => hwo x hx, hww, ?_⟩
      intro z hz
      rw [dotProduct_comm]
      exact mem_orth_one.1 hz w hwv

theorem edge_orth {u v : Lab m} (h : EdgeOK v u) : EdgeOK (orth 1 u) (orth 1 v) :=
  h.elim (fun e => Or.inl (up_orth e)) (fun e => Or.inr (up_orth e))

theorem width_orth {u v : Lab m} (h : EdgeOK v u) : Fd (orth 1 u) (orth 1 v) = Fd v u := by
  rw [Fd_eq_natAbs (edge_orth h), Fd_eq_natAbs h]
  have hu := finrank_compl (nondeg_of_edge_right h)
  have hv := finrank_compl (nondeg_of_edge_left h)
  omega

end CxMirrorProof

open IntMul.Kappa.R6.Cx NetLabels CxChunkMirror

theorem solution {R : Type} [DecidableEq R] {m : ℕ} [Fintype R]
    (cs : List (GChunk R m)) (lab : R → Lab m) (valid : ProgValid cs lab) :
    let b := backwardProgram (orth 1) cs
    ProgValid b (orth 1 ∘ progLab cs lab) ∧
      progLab b (orth 1 ∘ progLab cs lab) = orth 1 ∘ lab ∧
      progWidths b = (progWidths cs).reverse := by
  obtain ⟨validMirror, endpoints⟩ :=
    CxMirrorProof.backwardProgram_sound (orth 1) CxMirrorProof.edge_orth cs lab valid
  exact ⟨validMirror, endpoints,
    CxMirrorProof.backwardProgram_widths (orth 1) CxMirrorProof.width_orth cs lab valid⟩
