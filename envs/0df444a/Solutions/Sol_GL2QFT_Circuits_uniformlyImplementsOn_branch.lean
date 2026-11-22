-- Prove2me | solution 1 for GL2QFT.Circuits.uniformlyImplementsOn_branch
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:53:33.846282+00:00
-- url     : https://prove2.me/submissions/44dc9a98-a9d9-4bf0-a021-63dd80156f44

import Definitions.Def_GL2QFT_Circuits_Combinators
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_sum

set_option autoImplicit false

noncomputable section

open Classical
open scoped BigOperators
open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_Branch_Aux

def boolProdEquivSum (α : Type) : Bool × α ≃ α ⊕ α where
  toFun p := if p.1 then .inr p.2 else .inl p.2
  invFun
    | .inl a => (false, a)
    | .inr a => (true, a)
  left_inv p := by rcases p with ⟨_ | _, _⟩ <;> rfl
  right_inv s := by cases s <;> rfl

lemma padTo_sumCode_eq_padTo_boolAppCode {X : Type} {m w : ℕ} (c : X → Qubits m) (p : Bool × X) :
    padTo w (sumCode c c (boolProdEquivSum X p)) = padTo w (boolAppCode c p) := by
  funext a
  rcases p with ⟨b, x⟩
  have hmax : max m m = m := Nat.max_self m
  by_cases ha0 : a.val = 0
  · have h1 : a.val < 1 + max m m := by omega
    have h2 : a.val < 1 + m := by omega
    cases b <;> simp only [boolProdEquivSum, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte,
      sumCode, boolAppCode, padTo]
    · rw [dif_pos h1, dif_pos h2]
      have ha_eq1 : (⟨a.val, h1⟩ : Fin (1 + max m m)) = Fin.castAdd (max m m) 0 := Fin.ext ha0
      have ha_eq2 : (⟨a.val, h2⟩ : Fin (1 + m)) = Fin.castAdd m 0 := Fin.ext ha0
      rw [ha_eq1, ha_eq2, Fin.append_left, Fin.append_left]
    · rw [dif_pos h1, dif_pos h2]
      have ha_eq1 : (⟨a.val, h1⟩ : Fin (1 + max m m)) = Fin.castAdd (max m m) 0 := Fin.ext ha0
      have ha_eq2 : (⟨a.val, h2⟩ : Fin (1 + m)) = Fin.castAdd m 0 := Fin.ext ha0
      rw [ha_eq1, ha_eq2, Fin.append_left, Fin.append_left]
  · obtain ⟨k, hk⟩ : ∃ k, a.val = k + 1 := ⟨a.val - 1, by omega⟩
    by_cases hkm : k < m
    · have h1 : a.val < 1 + max m m := by omega
      have h2 : a.val < 1 + m := by omega
      have ha_eq1 : (⟨a.val, h1⟩ : Fin (1 + max m m)) = Fin.natAdd 1 ⟨k, by omega⟩ :=
        Fin.ext (by simp [Fin.val_natAdd, hk]; omega)
      have ha_eq2 : (⟨a.val, h2⟩ : Fin (1 + m)) = Fin.natAdd 1 ⟨k, hkm⟩ :=
        Fin.ext (by simp [Fin.val_natAdd, hk]; omega)
      cases b <;> simp only [boolProdEquivSum, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte,
        sumCode, boolAppCode, padTo]
      · rw [dif_pos h1, dif_pos h2, ha_eq1, ha_eq2, Fin.append_right, Fin.append_right]
        simp [padTo, hkm]
      · rw [dif_pos h1, dif_pos h2, ha_eq1, ha_eq2, Fin.append_right, Fin.append_right]
        simp [padTo, hkm]
    · have h1 : ¬ (a.val < 1 + max m m) := by omega
      have h2 : ¬ (a.val < 1 + m) := by omega
      cases b <;> simp only [boolProdEquivSum, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte,
        sumCode, boolAppCode, padTo]
      · rw [dif_neg h1, dif_neg h2]
      · rw [dif_neg h1, dif_neg h2]

lemma sumMat_eq_ctrlMat {X Y : Type} (Φ₀ Φ₁ : Matrix Y X ℂ) (q : Bool × Y) (p : Bool × X) :
    sumMat Φ₀ Φ₁ (boolProdEquivSum Y q) (boolProdEquivSum X p) = ctrlMat Φ₀ Φ₁ q p := by
  rcases q with ⟨_ | _, _⟩ <;> rcases p with ⟨_ | _, _⟩ <;>
    simp [boolProdEquivSum, sumMat, ctrlMat]

lemma embedVec_equiv {A B : Type} [Fintype A] [Fintype B] {w : ℕ}
    (e : A ≃ B) (cA : A → Qubits w) (cB : B → Qubits w)
    (hc : ∀ a, cB (e a) = cA a) (φ : EuclideanSpace ℂ A) :
    embedVec cB (WithLp.toLp 2 (fun b => φ.ofLp (e.symm b))) = embedVec cA φ := by
  apply WithLp.ofLp_injective; funext y
  simp only [embedVec, WithLp.ofLp_toLp]
  rw [← Fintype.sum_equiv e _ _ (fun a => ?_)]
  simp [hc a, e.left_inv a]

end GL2QFT_Branch_Aux

theorem solution {P : FieldData → Prop} {X Y : FieldData → Type}
    [∀ D, Fintype (X D)] [∀ D, Fintype (Y D)] {inW outW : FieldData → ℕ}
    {cin : ∀ D, X D → Qubits (inW D)} {cout : ∀ D, Y D → Qubits (outW D)}
    {Φ₀ Φ₁ : ∀ D, Matrix (Y D) (X D) ℂ}
    (h0 : UniformlyImplementsOn P cin cout Φ₀)
    (h1 : UniformlyImplementsOn P cin cout Φ₁) :
    UniformlyImplementsOn P (fun D => boolAppCode (cin D)) (fun D => boolAppCode (cout D))
      (fun D => ctrlMat (Φ₀ D) (Φ₁ D)) := by
  have hsum := GL2QFT.Circuits.uniformlyImplementsOn_sum h0 h1
  obtain ⟨wires, circ, f, c, hf_poly, hf_spec, hlen, himp⟩ := hsum
  refine ⟨wires, circ, f, c, hf_poly, hf_spec, hlen, ?_⟩
  intro D hD k
  obtain ⟨hin_w, hout_w, himp_k⟩ := himp D hD k
  have hin_w' : 1 + inW D ≤ wires D k := by simpa [Nat.max_self] using hin_w
  have hout_w' : 1 + outW D ≤ wires D k := by simpa [Nat.max_self] using hout_w
  refine ⟨hin_w', hout_w', ?_⟩
  intro ψ
  let eX := GL2QFT_Branch_Aux.boolProdEquivSum (X D)
  let eY := GL2QFT_Branch_Aux.boolProdEquivSum (Y D)
  let ψ' : EuclideanSpace ℂ (X D ⊕ X D) := WithLp.toLp 2 (fun u => ψ.ofLp (eX.symm u))
  have hnormψ : ‖ψ'‖ = ‖ψ‖ := by
    have hsq : ‖ψ'‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      rw [← Fintype.sum_equiv eX (fun p => ‖ψ.ofLp p‖ ^ 2) (fun u => ‖ψ'.ofLp u‖ ^ 2)
        (fun p => by simp [ψ', eX.left_inv])]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hemb_in : embedVec (fun p => padTo (wires D k) (boolAppCode (cin D) p)) ψ =
      embedVec (fun u => padTo (wires D k) (sumCode (cin D) (cin D) u)) ψ' := by
    symm
    exact GL2QFT_Branch_Aux.embedVec_equiv eX _ _
      (fun p => GL2QFT_Branch_Aux.padTo_sumCode_eq_padTo_boolAppCode (cin D) p) ψ
  have hmul : WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ'.ofLp) =
      WithLp.toLp 2 (fun v => ((ctrlMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp) (eY.symm v)) := by
    apply WithLp.ofLp_injective; funext v
    simp only [WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
    obtain ⟨q, rfl⟩ := eY.surjective v
    simp only [Equiv.symm_apply_apply]
    exact (Fintype.sum_equiv eX _ _ fun p => by
      simp only [ψ', WithLp.ofLp_toLp, Equiv.symm_apply_apply]
      rw [GL2QFT_Branch_Aux.sumMat_eq_ctrlMat]).symm
  have hemb_out : embedVec (fun q => padTo (wires D k) (boolAppCode (cout D) q))
        (WithLp.toLp 2 ((ctrlMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp)) =
      embedVec (fun v => padTo (wires D k) (sumCode (cout D) (cout D) v))
        (WithLp.toLp 2 ((sumMat (Φ₀ D) (Φ₁ D)).mulVec ψ'.ofLp)) := by
    rw [hmul]
    symm
    exact GL2QFT_Branch_Aux.embedVec_equiv eY _ _
      (fun q => GL2QFT_Branch_Aux.padTo_sumCode_eq_padTo_boolAppCode (cout D) q)
      (WithLp.toLp 2 ((ctrlMat (Φ₀ D) (Φ₁ D)).mulVec ψ.ofLp))
  rw [hemb_in, hemb_out, ← hnormψ]
  exact himp_k ψ'
