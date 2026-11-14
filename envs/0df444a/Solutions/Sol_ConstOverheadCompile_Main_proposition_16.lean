-- Prove2me | solution 1 for ConstOverheadCompile.Main.proposition_16
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T20:09:03.681683+00:00
-- url     : https://prove2.me/submissions/9574c258-8df5-4d47-898e-25aa2c1cd089

import Definitions.Def_ConstOverheadCompile_Main_Gadgets

open ConstOverheadCompile.Main QAlgorithms

private def mk4 (f : Bool → Bool → Bool → Bool → ℂ) : Qubits 4 → ℂ :=
  fun x => f (x 0) (x 1) (x 2) (x 3)

private lemma list_reverse_prod_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (v : ι → ℂ) :
    l.reverse.prod.mulVec v = l.foldl (fun w M => M.mulVec w) v := by
  induction l generalizing v with
  | nil => simp
  | cons M ms ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
      ← Matrix.mulVec_mulVec, List.foldl_cons, ih]

private lemma diag_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (d v : ι → ℂ) (x : ι) :
    (Matrix.diagonal d).mulVec v x = d x * v x := by
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

private lemma cnotApp_mulVec {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S)
    (a t : Fin 4) (hat : a ≠ t) (v : Qubits 4 → ℂ) :
    (embedOp (cnotApp h a t hat).gate.mat (cnotApp h a t hat).wires).mulVec v =
      fun x => v (fun k => if k = t then xor (x t) (x a) else x k) := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  let z0 : Qubits 4 := fun k => if k = t then xor (x t) (x a) else x k
  rw [Finset.sum_eq_single z0]
  · have hall : ∀ k : Fin 4, k ∉ Set.range (![a, t] : Fin 2 → Fin 4) → x k = z0 k := by
      intro k hk
      have hkt : k ≠ t := fun h_eq => hk ⟨1, h_eq.symm⟩
      simp [z0, hkt]
    have hemb : embedOp (cnotApp h a t hat).gate.mat (cnotApp h a t hat).wires x z0 =
        cnot (x a, x t) (z0 a, z0 t) := by
      change (if ∀ k : Fin 4, k ∉ Set.range (![a, t] : Fin 2 → Fin 4) → x k = z0 k
          then cnot (x a, x t) (z0 a, z0 t) else 0) = cnot (x a, x t) (z0 a, z0 t)
      rw [if_pos hall]
    have hza : z0 a = x a := by simp [z0, hat]
    have hzt : z0 t = xor (x t) (x a) := by simp [z0]
    rw [hemb, hza, hzt]
    have hc : cnot (x a, x t) (x a, xor (x t) (x a)) = 1 := by
      cases x a <;> cases x t <;> simp [cnot]
    rw [hc, one_mul]
  · intro z _ hz
    have hemb : embedOp (cnotApp h a t hat).gate.mat (cnotApp h a t hat).wires x z = 0 := by
      change (if ∀ k : Fin 4, k ∉ Set.range (![a, t] : Fin 2 → Fin 4) → x k = z k
          then cnot (x a, x t) (z a, z t) else 0) = 0
      by_cases hall : ∀ k : Fin 4, k ∉ Set.range (![a, t] : Fin 2 → Fin 4) → x k = z k
      · rw [if_pos hall]
        unfold cnot
        rw [Matrix.of_apply, if_neg]
        rintro ⟨h1, h2⟩
        dsimp only at h1 h2
        apply hz
        funext k
        by_cases hkt : k = t
        · subst hkt
          simp only [z0, ↓reduceIte]
          rw [h2, h1]
          cases z k <;> cases z a <;> rfl
        · simp only [z0, hkt, ↓reduceIte]
          by_cases hka : k = a
          · subst hka; exact h1.symm
          · exact (hall k (by
              rintro ⟨i, hi⟩
              fin_cases i
              · exact hka hi.symm
              · exact hkt hi.symm)).symm
      · rw [if_neg hall]
    rw [hemb, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ z0) hmem

private lemma toffoliApp_mulVec {S : Set Gate} (h : toffoli ∈ S) (v : Qubits 4 → ℂ) :
    (embedOp (toffoliApp h toffoliWires).gate.mat (toffoliApp h toffoliWires).wires).mulVec v =
      fun x => v (fun k => if k = 3 then xor (x 3) (x 1 && x 2) else x k) := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  let z0 : Qubits 4 := fun k => if k = 3 then xor (x 3) (x 1 && x 2) else x k
  rw [Finset.sum_eq_single z0]
  · have hall : ∀ k : Fin 4, k ∉ Set.range (![1, 2, 3] : Fin 3 → Fin 4) → x k = z0 k := by
      intro k hk
      have hk3 : k ≠ 3 := fun h_eq => hk ⟨2, h_eq.symm⟩
      simp [z0, hk3]
    have hemb : embedOp (toffoliApp h toffoliWires).gate.mat
          (toffoliApp h toffoliWires).wires x z0 =
        if x 1 = z0 1 ∧ x 2 = z0 2 ∧ x 3 = xor (z0 3) (z0 1 && z0 2) then 1 else 0 := by
      change (if ∀ k : Fin 4, k ∉ Set.range (![1, 2, 3] : Fin 3 → Fin 4) → x k = z0 k then
          (if x 1 = z0 1 ∧ x 2 = z0 2 ∧ x 3 = xor (z0 3) (z0 1 && z0 2) then (1 : ℂ) else 0)
        else 0) = _
      rw [if_pos hall]
    rw [hemb]
    have hcond : x 1 = z0 1 ∧ x 2 = z0 2 ∧ x 3 = xor (z0 3) (z0 1 && z0 2) := by
      refine ⟨by simp [z0], by simp [z0], ?_⟩
      simp only [z0, (by decide : (1 : Fin 4) ≠ 3), (by decide : (2 : Fin 4) ≠ 3), ↓reduceIte]
      cases x 3 <;> cases (x 1 && x 2) <;> rfl
    rw [if_pos hcond, one_mul]
  · intro z _ hz
    have hemb : embedOp (toffoliApp h toffoliWires).gate.mat
          (toffoliApp h toffoliWires).wires x z = 0 := by
      change (if ∀ k : Fin 4, k ∉ Set.range (![1, 2, 3] : Fin 3 → Fin 4) → x k = z k then
          (if x 1 = z 1 ∧ x 2 = z 2 ∧ x 3 = xor (z 3) (z 1 && z 2) then (1 : ℂ) else 0)
        else 0) = 0
      by_cases hall : ∀ k : Fin 4, k ∉ Set.range (![1, 2, 3] : Fin 3 → Fin 4) → x k = z k
      · rw [if_pos hall, if_neg]
        rintro ⟨h1, h2, h3⟩
        apply hz
        funext k
        by_cases hk3 : k = 3
        · subst hk3
          simp only [z0, ↓reduceIte]
          rw [h3, h1, h2]
          cases z 3 <;> cases (z 1 && z 2) <;> rfl
        · simp only [z0, hk3, ↓reduceIte]
          by_cases hk1 : k = 1
          · subst hk1; exact h1.symm
          · by_cases hk2 : k = 2
            · subst hk2; exact h2.symm
            · exact (hall k (by
                rintro ⟨i, hi⟩
                fin_cases i
                · exact hk1 hi.symm
                · exact hk2 hi.symm
                · exact hk3 hi.symm)).symm
      · rw [if_neg hall]
    rw [hemb, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ z0) hmem

private lemma app1_rot3_mulVec {S : Set Gate} (φ : ℝ) (h : Gate.ofMatrix1 (rot φ) ∈ S)
    (v : Qubits 4 → ℂ) :
    (embedOp (app1 (rot φ) h 3).gate.mat (app1 (rot φ) h 3).wires).mulVec v =
      fun x => (if x 3 then Complex.exp ((φ : ℂ) * Complex.I) else 1) * v x := by
  funext x
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single x]
  · have hall : ∀ k : Fin 4, k ∉ Set.range (fun _ : Fin 1 => (3 : Fin 4)) → x k = x k :=
      fun _ _ => rfl
    have hemb : embedOp (app1 (rot φ) h 3).gate.mat (app1 (rot φ) h 3).wires x x =
        rot φ (x 3) (x 3) := by
      change (if ∀ k : Fin 4, k ∉ Set.range (fun _ : Fin 1 => (3 : Fin 4)) → x k = x k
          then rot φ (x 3) (x 3) else 0) = rot φ (x 3) (x 3)
      rw [if_pos hall]
    rw [hemb]
    cases x 3 <;> simp [rot]
  · intro z _ hz
    have hemb : embedOp (app1 (rot φ) h 3).gate.mat (app1 (rot φ) h 3).wires x z = 0 := by
      change (if ∀ k : Fin 4, k ∉ Set.range (fun _ : Fin 1 => (3 : Fin 4)) → x k = z k
          then rot φ (x 3) (z 3) else 0) = 0
      by_cases hall : ∀ k : Fin 4, k ∉ Set.range (fun _ : Fin 1 => (3 : Fin 4)) → x k = z k
      · rw [if_pos hall]
        have hx3 : x 3 ≠ z 3 := by
          intro h3
          apply hz
          funext k
          fin_cases k
          · exact (hall 0 (by simp)).symm
          · exact (hall 1 (by simp)).symm
          · exact (hall 2 (by simp)).symm
          · exact h3.symm
        simp [rot, hx3]
      · rw [if_neg hall]
    rw [hemb, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ x) hmem

private lemma cnot10_mk4 {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S) (hat : (1 : Fin 4) ≠ 0)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (cnotApp h 1 0 hat).gate.mat (cnotApp h 1 0 hat).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f (xor b0 b1) b1 b2 b3) := by
  funext x; simp [cnotApp_mulVec, mk4]

private lemma cnot20_mk4 {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S) (hat : (2 : Fin 4) ≠ 0)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (cnotApp h 2 0 hat).gate.mat (cnotApp h 2 0 hat).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f (xor b0 b2) b1 b2 b3) := by
  funext x; simp [cnotApp_mulVec, mk4]

private lemma cnot01_mk4 {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S) (hat : (0 : Fin 4) ≠ 1)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (cnotApp h 0 1 hat).gate.mat (cnotApp h 0 1 hat).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f b0 (xor b1 b0) b2 b3) := by
  funext x; simp [cnotApp_mulVec, mk4]

private lemma cnot02_mk4 {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S) (hat : (0 : Fin 4) ≠ 2)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (cnotApp h 0 2 hat).gate.mat (cnotApp h 0 2 hat).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f b0 b1 (xor b2 b0) b3) := by
  funext x; simp [cnotApp_mulVec, mk4]

private lemma cnot03_mk4 {S : Set Gate} (h : Gate.ofMatrix2 cnot ∈ S) (hat : (0 : Fin 4) ≠ 3)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (cnotApp h 0 3 hat).gate.mat (cnotApp h 0 3 hat).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f b0 b1 b2 (xor b3 b0)) := by
  funext x; simp [cnotApp_mulVec, mk4]

private lemma toffoli_mk4 {S : Set Gate} (h : toffoli ∈ S)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (toffoliApp h toffoliWires).gate.mat (toffoliApp h toffoliWires).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => f b0 b1 b2 (xor b3 (b1 && b2))) := by
  funext x; simp [toffoliApp_mulVec, mk4]

private lemma rot3_mk4 {S : Set Gate} (φ : ℝ) (h : Gate.ofMatrix1 (rot φ) ∈ S)
    (f : Bool → Bool → Bool → Bool → ℂ) :
    (embedOp (app1 (rot φ) h 3).gate.mat (app1 (rot φ) h 3).wires).mulVec (mk4 f) =
      mk4 (fun b0 b1 b2 b3 => (if b3 then Complex.exp ((φ : ℂ) * Complex.I) else 1) * f b0 b1 b2 b3) := by
  funext x; simp [app1_rot3_mulVec, mk4]

theorem solution (θ : ℝ) (ψ φ : Bool → ℂ) :
    (phaseHalving θ).unitary.mulVec (vec4 (resourceVec θ) ψ φ (basisVec false)) =
      vec4 (resourceVec θ) ((rot θ).mulVec ψ) ((rot θ).mulVec φ) (basisVec false) := by
  have hv4 (u0 u1 u2 u3 : Bool → ℂ) :
      vec4 u0 u1 u2 u3 = mk4 (fun b0 b1 b2 b3 => u0 b0 * u1 b1 * u2 b2 * u3 b3) := rfl
  rw [hv4 (resourceVec θ) ψ φ (basisVec false), Circuit.unitary, list_reverse_prod_mulVec]
  unfold phaseHalving
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [cnot10_mk4, cnot20_mk4, cnot01_mk4, cnot02_mk4,
    toffoli_mk4, cnot03_mk4, rot3_mk4, cnot03_mk4,
    toffoli_mk4, cnot02_mk4, cnot01_mk4]
  have hexp : Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  funext x
  simp only [mk4, vec4, resourceVec, rot, diag_mulVec, hexp]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    dsimp only [plusVec, basisVec, xor] <;>
    simp only [Bool.true_and, Bool.false_and, Bool.true_bne, Bool.false_bne,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte] <;>
    ring
