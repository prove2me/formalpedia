-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_restrict
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:40:38.486066+00:00
-- url     : https://prove2.me/submissions/3030bfdf-cea3-4872-beea-e3ef25329c86

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_Restrict_Aux

noncomputable def extVec {A B : Type} [Fintype A] (ι : A → B) (v : EuclideanSpace ℂ A) :
    EuclideanSpace ℂ B :=
  WithLp.toLp 2 fun b => ∑ a : A, if ι a = b then v a else 0

lemma embedVec_extVec {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (code : B → Qubits n) (ι : A → B) (ψ : EuclideanSpace ℂ A) :
    embedVec code (extVec ι ψ) = embedVec (fun a => code (ι a)) ψ := by
  ext q
  simp only [embedVec, extVec]
  calc
    ∑ b : B, (if code b = q then ∑ a : A, (if ι a = b then ψ a else 0) else 0)
        = ∑ b : B, ∑ a : A, (if ι a = b then (if code b = q then ψ a else 0) else 0) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
    _ = ∑ a : A, ∑ b : B, (if ι a = b then (if code b = q then ψ a else 0) else 0) :=
          Finset.sum_comm
    _ = ∑ a : A, (if code (ι a) = q then ψ a else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.sum_ite_eq]

lemma norm_extVec {A B : Type} [Fintype A] [Fintype B]
    (ι : A → B) (hι : Function.Injective ι) (ψ : EuclideanSpace ℂ A) :
    ‖extVec ι ψ‖ = ‖ψ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  have hpt : ∀ b : B, ‖(extVec ι ψ) b‖ ^ 2 = ∑ a : A, if ι a = b then ‖ψ a‖ ^ 2 else 0 := by
    intro b
    by_cases hb : ∃ a₀ : A, ι a₀ = b
    · obtain ⟨a₀, ha₀⟩ := hb
      have hiff : ∀ a : A, ι a = b ↔ a = a₀ := fun a =>
        ⟨fun h => hι (h.trans ha₀.symm), fun h => h ▸ ha₀⟩
      simp only [extVec, hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · push Not at hb
      simp [extVec, hb]
  calc
    ∑ b : B, ‖(extVec ι ψ) b‖ ^ 2
        = ∑ b : B, ∑ a : A, (if ι a = b then ‖ψ a‖ ^ 2 else 0) :=
          Finset.sum_congr rfl fun b _ => hpt b
    _ = ∑ a : A, ∑ b : B, (if ι a = b then ‖ψ a‖ ^ 2 else 0) := Finset.sum_comm
    _ = ∑ a : A, ‖ψ a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp [Finset.sum_ite_eq]

lemma mulVec_extVec {X Y X' Y' : Type} [Fintype X] [Fintype Y] [Fintype X'] [Fintype Y']
    (Φ : Matrix Y X ℂ) (ιX : X' → X) (ιY : Y' → Y) (hιY : Function.Injective ιY)
    (hinv : ∀ x' y, (∀ y', ιY y' ≠ y) → Φ y (ιX x') = 0) (ψ : EuclideanSpace ℂ X') :
    WithLp.toLp 2 (Φ.mulVec (WithLp.ofLp (extVec ιX ψ))) =
      extVec ιY (WithLp.toLp 2 ((Φ.submatrix ιY ιX).mulVec (WithLp.ofLp ψ))) := by
  ext y
  change (Φ.mulVec (WithLp.ofLp (extVec ιX ψ))) y =
    ∑ y' : Y', if ιY y' = y then ((Φ.submatrix ιY ιX).mulVec (WithLp.ofLp ψ)) y' else 0
  have hlhs : (Φ.mulVec (WithLp.ofLp (extVec ιX ψ))) y = ∑ x' : X', Φ y (ιX x') * ψ x' := by
    simp only [Matrix.mulVec, dotProduct, extVec]
    calc
      ∑ x : X, Φ y x * ∑ x' : X', (if ιX x' = x then ψ x' else 0)
          = ∑ x : X, ∑ x' : X', (if ιX x' = x then Φ y x * ψ x' else 0) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x' _ => ?_
            split_ifs <;> simp
      _ = ∑ x' : X', ∑ x : X, (if ιX x' = x then Φ y x * ψ x' else 0) := Finset.sum_comm
      _ = ∑ x' : X', Φ y (ιX x') * ψ x' := by
            refine Finset.sum_congr rfl fun x' _ => ?_
            simp [Finset.sum_ite_eq]
  rw [hlhs]
  by_cases hy : ∃ y₀' : Y', ιY y₀' = y
  · obtain ⟨y₀', hy₀'⟩ := hy
    have hiff : ∀ y' : Y', ιY y' = y ↔ y' = y₀' := fun y' =>
      ⟨fun h => hιY (h.trans hy₀'.symm), fun h => h ▸ hy₀'⟩
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, hy₀']
  · push Not at hy
    have hzero : ∀ x' : X', Φ y (ιX x') = 0 := fun x' => hinv x' y hy
    simp [hy, hzero]

end GL2QFT_Restrict_Aux

theorem solution {P : FieldData → Prop} {X Y X' Y' : FieldData → Type} [∀ D, Fintype (X D)]
    [∀ D, Fintype (Y D)] [∀ D, Fintype (X' D)] [∀ D, Fintype (Y' D)] {inW outW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)}
    {Φ : ∀ D, Matrix (Y D) (X D) ℂ} (ιX : ∀ D, X' D → X D) (ιY : ∀ D, Y' D → Y D)
    (h : UniformlyImplementsOn P cin cout Φ)
    (hιX : ∀ D, P D → Function.Injective (ιX D))
    (hιY : ∀ D, P D → Function.Injective (ιY D))
    (hinv : ∀ D, P D → ∀ x' y, (∀ y', ιY D y' ≠ y) → Φ D y (ιX D x') = 0) :
    UniformlyImplementsOn P (fun D x' => cin D (ιX D x')) (fun D y' => cout D (ιY D y'))
      (fun D => (Φ D).submatrix (ιY D) (ιX D)) := by
  rcases h with ⟨wires, circ, f, c, hf, henc, hlen, himpl⟩
  refine ⟨wires, circ, f, c, hf, henc, hlen, fun D hD k => ?_⟩
  rcases himpl D hD k with ⟨hin, hout, hImp⟩
  refine ⟨hin, hout, fun ψ => ?_⟩
  have h1 := hImp (GL2QFT_Restrict_Aux.extVec (ιX D) ψ)
  rw [GL2QFT_Restrict_Aux.embedVec_extVec, GL2QFT_Restrict_Aux.mulVec_extVec (Φ D) (ιX D) (ιY D)
    (hιY D hD) (hinv D hD) ψ, GL2QFT_Restrict_Aux.embedVec_extVec,
    GL2QFT_Restrict_Aux.norm_extVec (ιX D) (hιX D hD) ψ] at h1
  exact h1
