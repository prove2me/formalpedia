-- Prove2me | solution 1 for ConstOverheadCompile.Main.state_injection
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T10:08:02.990507+00:00
-- url     : https://prove2.me/submissions/679a76b9-7777-43df-bf93-ce972422b5df

import Definitions.Def_ConstOverheadCompile_Main_Gadgets

open ConstOverheadCompile.Main QAlgorithms

private def qubits2Equiv : Qubits 2 ≃ Bool × Bool where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by cases p; rfl

private lemma sum_qubits2 (f : Qubits 2 → ℂ) :
    (∑ y : Qubits 2, f y) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [← qubits2Equiv.symm.sum_comp]
  simp only [qubits2Equiv, Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

private lemma diag_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (d v : ι → ℂ) (x : ι) :
    (Matrix.diagonal d).mulVec v x = d x * v x := by
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

theorem solution (θ : ℝ) (ψ : Bool → ℂ) :
    (AdaptiveCircuit.krausList (injectionGadget θ)).map
        (fun K => K.mulVec (vec2 ψ (resourceVec θ))) =
      [((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • vec2 ((rot θ).mulVec ψ) (basisVec false),
       (Complex.exp ((θ : ℂ) * Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
         vec2 ((rot θ).mulVec ψ) (basisVec true)] := by
  let gC : GateApp (injectionGates θ) 2 :=
    cnotApp (Or.inl (by simp [CliffordT])) 0 1 (by decide)
  let gR : GateApp (injectionGates θ) 2 :=
    app1 (rot (2 * θ)) (Or.inr rfl) 0
  let v0 : Qubits 2 → ℂ := vec2 ψ (resourceVec θ)
  have hC : (embedOp gC.gate.mat gC.wires).mulVec v0 =
      fun x => v0 ![x 0, xor (x 1) (x 0)] := by
    funext x
    rw [Matrix.mulVec, dotProduct, sum_qubits2]
    have hemb (z : Qubits 2) :
        embedOp gC.gate.mat gC.wires x z = cnot (x 0, x 1) (z 0, z 1) := by
      change (if ∀ a : Fin 2, a ∉ Set.range (![0, 1] : Fin 2 → Fin 2) → x a = z a
          then cnot (x 0, x 1) (z 0, z 1) else 0) = cnot (x 0, x 1) (z 0, z 1)
      have hall : ∀ a : Fin 2, a ∉ Set.range (![0, 1] : Fin 2 → Fin 2) → x a = z a := by
        intro a ha
        fin_cases a
        · exact absurd ⟨0, rfl⟩ ha
        · exact absurd ⟨1, rfl⟩ ha
      rw [if_pos hall]
    rw [hemb ![false, false], hemb ![false, true], hemb ![true, false], hemb ![true, true]]
    cases x 0 <;> cases x 1 <;> simp [cnot]
  have hexp : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hB0 : (AdaptiveCircuit.proj 1 false).mulVec ((embedOp gC.gate.mat gC.wires).mulVec v0) =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • vec2 ((rot θ).mulVec ψ) (basisVec false) := by
    rw [hC]
    funext x
    rw [AdaptiveCircuit.proj, diag_mulVec]
    simp only [v0, vec2, resourceVec, rot, Pi.smul_apply, smul_eq_mul, diag_mulVec]
    cases x 0 <;> cases x 1 <;>
      simp [plusVec, basisVec] <;>
      ring
  have hP1 : (AdaptiveCircuit.proj 1 true).mulVec ((embedOp gC.gate.mat gC.wires).mulVec v0) =
      fun x => if x 1 then v0 ![x 0, xor true (x 0)] else 0 := by
    rw [hC]
    funext x
    rw [AdaptiveCircuit.proj, diag_mulVec]
    cases x 1 <;> simp
  have hB1 : (embedOp gR.gate.mat gR.wires).mulVec
        ((AdaptiveCircuit.proj 1 true).mulVec ((embedOp gC.gate.mat gC.wires).mulVec v0)) =
      (Complex.exp ((θ : ℂ) * Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
        vec2 ((rot θ).mulVec ψ) (basisVec true) := by
    rw [hP1]
    funext x
    rw [Matrix.mulVec, dotProduct, sum_qubits2]
    have hemb (z : Qubits 2) :
        embedOp gR.gate.mat gR.wires x z =
          if x 1 = z 1 then rot (2 * θ) (x 0) (z 0) else 0 := by
      change (if ∀ a : Fin 2, a ∉ Set.range (fun _ : Fin 1 => (0 : Fin 2)) → x a = z a
          then rot (2 * θ) (x 0) (z 0) else 0) =
        if x 1 = z 1 then rot (2 * θ) (x 0) (z 0) else 0
      by_cases hyz : x 1 = z 1
      · have hall : ∀ a : Fin 2, a ∉ Set.range (fun _ : Fin 1 => (0 : Fin 2)) → x a = z a := by
          intro a ha
          fin_cases a
          · exact absurd ⟨0, rfl⟩ ha
          · exact hyz
        rw [if_pos hall, if_pos hyz]
      · have hnall : ¬ (∀ a : Fin 2, a ∉ Set.range (fun _ : Fin 1 => (0 : Fin 2)) → x a = z a) := by
          intro hall
          exact hyz (hall 1 (by simp))
        rw [if_neg hnall, if_neg hyz]
    rw [hemb ![false, false], hemb ![false, true], hemb ![true, false], hemb ![true, true]]
    simp only [v0, vec2, resourceVec, rot, Pi.smul_apply, smul_eq_mul, diag_mulVec, hexp]
    cases x 0 <;> cases x 1 <;>
      simp [plusVec, basisVec] <;>
      ring
  change [((1 * AdaptiveCircuit.proj 1 false) * embedOp gC.gate.mat gC.wires).mulVec v0,
          (((1 * embedOp gR.gate.mat gR.wires) * AdaptiveCircuit.proj 1 true) *
            embedOp gC.gate.mat gC.wires).mulVec v0] = _
  simp only [one_mul, ← Matrix.mulVec_mulVec]
  rw [hB0, hB1]
