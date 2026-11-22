-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_unpad_out
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:46:36.463683+00:00
-- url     : https://prove2.me/submissions/49d4c052-ad4c-4a0d-b18b-928b2676d8ce

import Definitions.Def_GL2QFT_Uniform

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_UnpadOut_Aux

lemma padTo_append_false {w m : ℕ} (s : Qubits m) :
    padTo w (Fin.append s (fun (_ : Fin 1) => false)) = padTo w s := by
  funext i
  by_cases hm : i.val < m
  · have hm1 : i.val < m + 1 := Nat.lt_succ_of_lt hm
    simp only [padTo, dif_pos hm, dif_pos hm1]
    have hcast : (⟨i.val, hm1⟩ : Fin (m + 1)) = Fin.castAdd 1 ⟨i.val, hm⟩ := by
      ext; rfl
    rw [hcast, Fin.append_left]
  · simp only [padTo, dif_neg hm]
    by_cases hm1 : i.val < m + 1
    · rw [dif_pos hm1]
      have hval : i.val = m := by omega
      have hcast : (⟨i.val, hm1⟩ : Fin (m + 1)) = Fin.natAdd m (0 : Fin 1) := by
        ext; exact hval
      rw [hcast, Fin.append_right]
    · rw [dif_neg hm1]

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

lemma mulVec_eq_extVec {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (Φz : Matrix Z X ℂ) (ι : Y → Z) (hι : Function.Injective ι)
    (hvan : ∀ z x, (∀ y, ι y ≠ z) → Φz z x = 0) (ψ : EuclideanSpace ℂ X) :
    WithLp.toLp 2 (Φz.mulVec (WithLp.ofLp ψ)) =
      extVec ι (WithLp.toLp 2 ((Matrix.of fun y x => Φz (ι y) x).mulVec (WithLp.ofLp ψ))) := by
  ext z
  change (Φz.mulVec (WithLp.ofLp ψ)) z =
    ∑ y : Y, if ι y = z then ((Matrix.of fun y x => Φz (ι y) x).mulVec (WithLp.ofLp ψ)) y else 0
  by_cases hz : ∃ y₀ : Y, ι y₀ = z
  · obtain ⟨y₀, hy₀⟩ := hz
    have hiff : ∀ y : Y, ι y = z ↔ y = y₀ := fun y =>
      ⟨fun h => hι (h.trans hy₀.symm), fun h => h ▸ hy₀⟩
    simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Matrix.mulVec, dotProduct, Matrix.of_apply, hy₀]
  · push Not at hz
    have hzero : ∀ x : X, Φz z x = 0 := fun x => hvan z x hz
    simp [Matrix.mulVec, dotProduct, hz, hzero]

end GL2QFT_UnpadOut_Aux

theorem solution {P : FieldData → Prop} {X Y Z : FieldData → Type} [∀ D, Fintype (X D)]
    [∀ D, Fintype (Y D)] [∀ D, Fintype (Z D)] {inW outW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)}
    {cz : ∀ D, Z D → Qubits (outW D + 1)} {Φz : ∀ D, Matrix (Z D) (X D) ℂ}
    (ι : ∀ D, Y D → Z D) (h : UniformlyImplementsOn P cin cz Φz)
    (hι : ∀ D, P D → Function.Injective (ι D))
    (hpad : ∀ D y, cz D (ι D y) = Fin.append (cout D y) (fun (_ : Fin 1) => false))
    (hvan : ∀ D, P D → ∀ z x, (∀ y, ι D y ≠ z) → Φz D z x = 0) :
    UniformlyImplementsOn P cin cout (fun D => Matrix.of fun y x => Φz D (ι D y) x) := by
  rcases h with ⟨wires, circ, f, c, hf, henc, hlen, himpl⟩
  refine ⟨wires, circ, f, c, hf, henc, hlen, fun D hD k => ?_⟩
  rcases himpl D hD k with ⟨hin, hout1, hImp⟩
  refine ⟨hin, Nat.le_of_succ_le hout1, fun ψ => ?_⟩
  have h1 := hImp ψ
  rw [GL2QFT_UnpadOut_Aux.mulVec_eq_extVec (Φz D) (ι D) (hι D hD) (hvan D hD) ψ,
    GL2QFT_UnpadOut_Aux.embedVec_extVec] at h1
  have hcode : (fun y => padTo (wires D k) (cz D (ι D y))) =
      (fun y => padTo (wires D k) (cout D y)) := by
    funext y
    rw [hpad D y, GL2QFT_UnpadOut_Aux.padTo_append_false]
  rw [hcode] at h1
  exact h1
