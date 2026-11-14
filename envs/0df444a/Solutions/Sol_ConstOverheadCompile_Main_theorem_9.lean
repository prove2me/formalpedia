-- Prove2me | solution 1 for ConstOverheadCompile.Main.theorem_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T23:44:03.557735+00:00
-- url     : https://prove2.me/submissions/a2067d6c-cad0-436b-8c32-ce38a1c66843
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit
import Definitions.Def_ConstOverheadCompile_Main_Gadgets
import Theorems.Thm_ConstOverheadCompile_Main_ross_selinger_synthesis
import Theorems.Thm_ConstOverheadCompile_Main_binomial_tail_eq16
import Theorems.Thm_ConstOverheadCompile_Main_state_injection
import Theorems.Thm_ConstOverheadCompile_Main_proposition_16

open scoped Kronecker Matrix MatrixOrder ComplexOrder

section Thm9SharedDefs

def t9_ket0Anc (a : ℕ) : QAlgorithms.Qubits a → ℂ :=
  fun z => if z = (fun _ => false) then 1 else 0

def t9_tensorAncVec {n a m_ref : ℕ} (χ : QAlgorithms.Qubits a → ℂ)
    (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ) :
    Matrix (Fin m_ref × QAlgorithms.Qubits (n + a)) (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ :=
  Matrix.of fun p₁ p₂ =>
    ρ (p₁.1, fun i => p₁.2 (Fin.castAdd a i)) (p₂.1, fun i => p₂.2 (Fin.castAdd a i)) *
      χ (fun j => p₁.2 (Fin.natAdd n j)) * star (χ (fun j => p₂.2 (Fin.natAdd n j)))

def t9_partialTraceAnc {n a m_ref : ℕ}
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits (n + a))
      (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ) :
    Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ :=
  Matrix.of fun p₁ p₂ =>
    ∑ j : QAlgorithms.Qubits a, σ (p₁.1, Fin.append p₁.2 j) (p₂.1, Fin.append p₂.2 j)

noncomputable def t9_productAncVec {L M : ℕ} (α : Fin L → ℝ)
    (z : QAlgorithms.Qubits (L + M)) : ℂ :=
  (∏ i : Fin L, ConstOverheadCompile.Main.resourceVec (α i) (z (Fin.castAdd M i))) *
    (∏ j : Fin M, ConstOverheadCompile.Main.basisVec false (z (Fin.natAdd L j)))

def t9_liftAncCircuit {S : Set QAlgorithms.Gate} (n : ℕ) {a : ℕ}
    (c : QAlgorithms.Circuit S a) : QAlgorithms.Circuit S (n + a) :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩⟩

def t9_prependCircuit {S : Set QAlgorithms.Gate} {N : ℕ}
    (c : QAlgorithms.Circuit S N)
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S N) :
    ConstOverheadCompile.Main.AdaptiveCircuit S N :=
  c.foldr ConstOverheadCompile.Main.AdaptiveCircuit.gate B

def t9_setWire {N : ℕ} (q : Fin N) (b : Bool) (x : QAlgorithms.Qubits N) :
    QAlgorithms.Qubits N :=
  Function.update x q b

def t9_traceAndSetWire {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ) :
    Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ :=
  Matrix.of fun p₁ p₂ =>
    (∑ b : Bool, σ (p₁.1, t9_setWire q b p₁.2) (p₂.1, t9_setWire q b p₂.2)) *
      v (p₁.2 q) * star (v (p₂.2 q))

def t9_HasPureWire {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ) : Prop :=
  t9_traceAndSetWire q v σ = σ

def t9_unitConj {N m_ref : ℕ} (U : Matrix (QAlgorithms.Qubits N) (QAlgorithms.Qubits N) ℂ)
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ) :
    Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ :=
  ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ U) * σ *
    ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ U)ᴴ

noncomputable def t9_rotOnWire {N : ℕ} (θ : ℝ) (q : Fin N) :
    Matrix (QAlgorithms.Qubits N) (QAlgorithms.Qubits N) ℂ :=
  QAlgorithms.embedOp (QAlgorithms.Gate.ofMatrix1 (ConstOverheadCompile.Main.rot θ)).mat
    (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N)

theorem t9_cnot_mem_cliffordT :
    QAlgorithms.Gate.ofMatrix2 QAlgorithms.cnot ∈ ConstOverheadCompile.Main.CliffordT := by
  simp [ConstOverheadCompile.Main.CliffordT]

theorem t9_prependCircuit_maxGates {S : Set QAlgorithms.Gate} {N : ℕ}
    (c : QAlgorithms.Circuit S N)
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S N) :
    (t9_prependCircuit c B).maxGates = c.size + B.maxGates := by
  induction c with
  | nil => simp [t9_prependCircuit, QAlgorithms.Circuit.size]
  | cons g cs ih =>
      simp only [t9_prependCircuit, List.foldr_cons,
        ConstOverheadCompile.Main.AdaptiveCircuit.maxGates]
      rw [← t9_prependCircuit, ih]
      simp only [QAlgorithms.Circuit.size, List.length_cons]
      omega

theorem t9_liftAncCircuit_size {S : Set QAlgorithms.Gate} (n : ℕ) {a : ℕ}
    (c : QAlgorithms.Circuit S a) :
    (t9_liftAncCircuit n c).size = c.size := by
  simp [t9_liftAncCircuit, QAlgorithms.Circuit.size]

structure Thm9Step1API : Prop where
  cliffordT_isUnitary : ∀ g ∈ ConstOverheadCompile.Main.CliffordT, g.IsUnitary
  traceDist_self : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ),
    WildeQIT.traceDist A A = 0
  traceNorm_add_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ},
    X.IsHermitian → Y.IsHermitian →
    WildeQIT.traceNorm (X + Y) ≤ WildeQIT.traceNorm X + WildeQIT.traceNorm Y
  traceDist_triangle : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ},
    A.IsHermitian → B.IsHermitian → C.IsHermitian →
    WildeQIT.traceDist A C ≤ WildeQIT.traceDist A B + WildeQIT.traceDist B C
  traceNorm_smul_of_nonneg : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℝ},
    0 ≤ c → ∀ {X : Matrix ι ι ℂ}, X.IsHermitian →
    WildeQIT.traceNorm ((c : ℂ) • X) = c * WildeQIT.traceNorm X
  isDensityOperator_conj_unitary : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {ρ U : Matrix ι ι ℂ},
    WildeQIT.IsDensityOperator ρ → U ∈ Matrix.unitaryGroup ι ℂ →
    WildeQIT.IsDensityOperator (U * ρ * Uᴴ)
  cptp_traceNorm_le : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)), (ks.map fun K => Kᴴ * K).sum = 1 →
    ∀ {X : Matrix ι ι ℂ}, X.IsHermitian →
    WildeQIT.traceNorm ((ks.map fun K => K * X * Kᴴ).sum) ≤ WildeQIT.traceNorm X
  proj_decomp_density : ∀ {m n : ℕ} (q : Fin n)
    {ρ : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ},
    WildeQIT.IsDensityOperator ρ →
    ∃ (pf pt : ℝ)
      (ρf ρt : Matrix (Fin m × QAlgorithms.Qubits n) (Fin m × QAlgorithms.Qubits n) ℂ),
      0 ≤ pf ∧ 0 ≤ pt ∧ pf + pt = 1 ∧
      WildeQIT.IsDensityOperator ρf ∧ WildeQIT.IsDensityOperator ρt ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q false)ᴴ =
        (pf : ℂ) • ρf ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ConstOverheadCompile.Main.AdaptiveCircuit.proj q true)ᴴ =
        (pt : ℂ) • ρt
  traceDist_density_le_two : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ₁ σ₂ : Matrix ι ι ℂ},
    WildeQIT.IsDensityOperator σ₁ → WildeQIT.IsDensityOperator σ₂ →
    WildeQIT.traceDist σ₁ σ₂ ≤ 2
  isHermitian_channelRef : ∀ {S : Set QAlgorithms.Gate} {N m_ref : ℕ}
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S N)
    {X : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ},
    X.IsHermitian → (B.channelRef m_ref X).IsHermitian
  dataChannelRef_eq : ∀ {S : Set QAlgorithms.Gate} {n a : ℕ}
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S (n + a)) (m_ref : ℕ)
    (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ),
    B.dataChannelRef m_ref ρ =
      t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec (t9_ket0Anc a) ρ))
  prependAnc_dataChannelRef : ∀ {S : Set QAlgorithms.Gate} {n a : ℕ}
    (cAnc : QAlgorithms.Circuit S a)
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S (n + a)) (m_ref : ℕ)
    (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ),
    (t9_prependCircuit (t9_liftAncCircuit n cAnc) B).dataChannelRef m_ref ρ =
      t9_partialTraceAnc
        (B.channelRef m_ref (t9_tensorAncVec (cAnc.unitary.mulVec (t9_ket0Anc a)) ρ))
  isHermitian_partialTraceAnc : ∀ {n a m_ref : ℕ}
    {X : Matrix (Fin m_ref × QAlgorithms.Qubits (n + a))
      (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ},
    X.IsHermitian → (t9_partialTraceAnc X).IsHermitian
  partialTraceAnc_traceNorm_le : ∀ {n a m_ref : ℕ}
    {X : Matrix (Fin m_ref × QAlgorithms.Qubits (n + a))
      (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ},
    X.IsHermitian → WildeQIT.traceNorm (t9_partialTraceAnc X) ≤ WildeQIT.traceNorm X
  isDensityOperator_tensorAncVec : ∀ {n a m_ref : ℕ}
    {χ : QAlgorithms.Qubits a → ℂ}, (∑ z : QAlgorithms.Qubits a, ‖χ z‖ ^ 2) = 1 →
    ∀ {ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ},
    WildeQIT.IsDensityOperator ρ → WildeQIT.IsDensityOperator (t9_tensorAncVec χ ρ)
  isDensityOperator_partialTraceAnc : ∀ {n a m_ref : ℕ}
    {σ : Matrix (Fin m_ref × QAlgorithms.Qubits (n + a))
      (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ},
    WildeQIT.IsDensityOperator σ → WildeQIT.IsDensityOperator (t9_partialTraceAnc σ)
  channelWithAnc_approx_le : ∀ {S : Set QAlgorithms.Gate},
    (∀ g ∈ S, g.IsUnitary) → ∀ {n a : ℕ}
    (B : ConstOverheadCompile.Main.AdaptiveCircuit S (n + a))
    {χ₁ χ₂ : QAlgorithms.Qubits a → ℂ},
    (∑ z : QAlgorithms.Qubits a, ‖χ₁ z‖ ^ 2) = 1 →
    (∑ z : QAlgorithms.Qubits a, ‖χ₂ z‖ ^ 2) = 1 →
    ∀ {δ : ℝ}, 0 ≤ δ → ∀ (Φ : ℝ),
    Real.sqrt (∑ z : QAlgorithms.Qubits a,
      ‖Complex.exp ((Φ : ℂ) * Complex.I) * χ₁ z - χ₂ z‖ ^ 2) ≤ δ →
    ∀ (m_ref : ℕ)
    {ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ},
    WildeQIT.IsDensityOperator ρ →
    WildeQIT.traceDist
      (t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec χ₁ ρ)))
      (t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec χ₂ ρ))) ≤ 2 * δ
  prep_resource_states : ∀ {C_RS ε₀ : ℝ}, 0 < C_RS → 0 < ε₀ →
    (∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        ∀ U : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ,
          U ∈ Matrix.unitaryGroup (QAlgorithms.Qubits k) ℂ →
          ∃ c : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT k,
            (c.size : ℝ) ≤ C_RS * Real.log (1 / ε) ∧
            QAlgorithms.ApproxUpToPhase U c.unitary ε) →
    ∀ (L M : ℕ), 1 ≤ L → ∀ (α : Fin L → ℝ) {δ_tot : ℝ}, 0 < δ_tot →
      ∃ (cPrep : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT (L + M)) (Φ : ℝ),
        (cPrep.size : ℝ) ≤ (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) ∧
        (∑ z : QAlgorithms.Qubits (L + M),
          ‖(cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z‖ ^ 2) = 1 ∧
        (∑ z : QAlgorithms.Qubits (L + M), ‖t9_productAncVec α z‖ ^ 2) = 1 ∧
        Real.sqrt (∑ z : QAlgorithms.Qubits (L + M),
          ‖Complex.exp ((Φ : ℂ) * Complex.I) *
            (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z -
            t9_productAncVec α z‖ ^ 2) ≤ δ_tot

structure Thm9Step2API : Prop where
  hasPureWire_productAncVec_left : ∀ {n L M m_ref : ℕ} (α : Fin L → ℝ)
    (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ)
    (i : Fin L),
    t9_HasPureWire (Fin.natAdd n (Fin.castAdd M i)) (ConstOverheadCompile.Main.resourceVec (α i))
      (t9_tensorAncVec (t9_productAncVec α) ρ)
  hasPureWire_productAncVec_right : ∀ {n L M m_ref : ℕ} (α : Fin L → ℝ)
    (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ)
    (j : Fin M),
    t9_HasPureWire (Fin.natAdd n (Fin.natAdd L j)) (ConstOverheadCompile.Main.basisVec false)
      (t9_tensorAncVec (t9_productAncVec α) ρ)
  hasPureWire_traceAndSet_self : ∀ {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ),
    ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1 →
    ∀ (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ),
    t9_HasPureWire q v (t9_traceAndSetWire q v σ)
  hasPureWire_traceAndSet_other : ∀ {N m_ref : ℕ} {q q' : Fin N}, q ≠ q' →
    ∀ (v u : Bool → ℂ)
    {σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ},
    t9_HasPureWire q' u σ → t9_HasPureWire q' u (t9_traceAndSetWire q v σ)
  traceAndSetWire_unitConj_embedOp : ∀ {k N m_ref : ℕ}
    (M : Matrix (QAlgorithms.Qubits k) (QAlgorithms.Qubits k) ℂ)
    (w : Fin k ↪ Fin N) {q : Fin N}, q ∉ Set.range w → ∀ (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ),
    t9_unitConj (QAlgorithms.embedOp M w) (t9_traceAndSetWire q v σ) =
      t9_traceAndSetWire q v (t9_unitConj (QAlgorithms.embedOp M w) σ)
  traceAndSetWire_unitConj_proj : ∀ {N m_ref : ℕ} {q' q : Fin N}, q ≠ q' → ∀ (b : Bool)
    (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ),
    t9_unitConj (ConstOverheadCompile.Main.AdaptiveCircuit.proj q' b)
        (t9_traceAndSetWire q v σ) =
      t9_traceAndSetWire q v
        (t9_unitConj (ConstOverheadCompile.Main.AdaptiveCircuit.proj q' b) σ)
  partialTraceAnc_traceAndSetWire : ∀ {n a m_ref : ℕ} (u : Fin a) (v : Bool → ℂ),
    ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1 →
    ∀ (σ : Matrix (Fin m_ref × QAlgorithms.Qubits (n + a))
      (Fin m_ref × QAlgorithms.Qubits (n + a)) ℂ),
    t9_partialTraceAnc (t9_traceAndSetWire (Fin.natAdd n u) v σ) = t9_partialTraceAnc σ
  norm_sq_resourceVec : ∀ θ : ℝ,
    ‖ConstOverheadCompile.Main.resourceVec θ false‖ ^ 2 +
      ‖ConstOverheadCompile.Main.resourceVec θ true‖ ^ 2 = 1
  norm_sq_plusVec :
    ‖ConstOverheadCompile.Main.plusVec false‖ ^ 2 +
      ‖ConstOverheadCompile.Main.plusVec true‖ ^ 2 = 1
  norm_sq_basisVec : ∀ b : Bool,
    ‖ConstOverheadCompile.Main.basisVec b false‖ ^ 2 +
      ‖ConstOverheadCompile.Main.basisVec b true‖ ^ 2 = 1
  rotOnWire_zero : ∀ {N : ℕ} (q : Fin N), t9_rotOnWire 0 q = 1
  rotOnWire_two_pi_nat : ∀ {N : ℕ} (k : ℕ) (q : Fin N),
    t9_rotOnWire (2 * Real.pi * (k : ℝ)) q = 1
  rotOnWire_add : ∀ {N : ℕ} (α β : ℝ) (q : Fin N),
    t9_rotOnWire (α + β) q = t9_rotOnWire α q * t9_rotOnWire β q
  stateInjection_step :
    ∃ (resetFalse resetTrue : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 1),
      resetFalse.size ≤ 1 ∧ resetTrue.size ≤ 5 ∧
      ∀ (N m_ref : ℕ) (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank) (θ : ℝ)
        (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ),
        t9_HasPureWire w_bank (ConstOverheadCompile.Main.resourceVec θ) σ →
        let w1_bank : Fin 1 ↪ Fin N := ⟨fun _ => w_bank, fun i j _ => Subsingleton.elim i j⟩
        let g_cnot := ConstOverheadCompile.Main.cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne
        let σ_cnot := t9_unitConj (QAlgorithms.embedOp g_cnot.gate.mat g_cnot.wires) σ
        let P (b : Bool) := ConstOverheadCompile.Main.AdaptiveCircuit.proj w_bank b
        t9_unitConj (QAlgorithms.embedOp resetFalse.unitary w1_bank)
            (t9_unitConj (P false) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire θ w_targ)
              (t9_traceAndSetWire w_bank ConstOverheadCompile.Main.plusVec σ) ∧
        t9_unitConj (QAlgorithms.embedOp resetTrue.unitary w1_bank)
            (t9_unitConj (P true) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire (-θ) w_targ)
              (t9_traceAndSetWire w_bank ConstOverheadCompile.Main.plusVec σ)
  phaseHalving_split :
    ∃ (half1 half2 : QAlgorithms.Circuit ConstOverheadCompile.Main.CliffordT 4),
      half1.size ≤ 38 ∧ half2.size ≤ 36 ∧
      ∀ (N m_ref : ℕ) (w : Fin 4 ↪ Fin N) (θ : ℝ)
        (σ : Matrix (Fin m_ref × QAlgorithms.Qubits N) (Fin m_ref × QAlgorithms.Qubits N) ℂ),
        t9_HasPureWire (w 0) (ConstOverheadCompile.Main.resourceVec θ) σ →
        t9_HasPureWire (w 2) ConstOverheadCompile.Main.plusVec σ →
        t9_HasPureWire (w 3) (ConstOverheadCompile.Main.basisVec false) σ →
        t9_unitConj (QAlgorithms.embedOp half2.unitary w)
          (t9_unitConj (t9_rotOnWire (2 * θ) (w 3))
            (t9_unitConj (QAlgorithms.embedOp half1.unitary w) σ)) =
          t9_unitConj (t9_rotOnWire θ (w 1))
            (t9_traceAndSetWire (w 2) (ConstOverheadCompile.Main.resourceVec θ) σ)

def Thm9Step3Type : Prop :=
  Thm9Step1API → Thm9Step2API →
    (∀ (r : ℕ), 2 ≤ r → ∀ (ε : ℝ), 0 < ε → ∀ (n G : ℕ)
      (A : ConstOverheadCompile.Main.AdaptiveCircuit
        (ConstOverheadCompile.Main.CliffordT ∪
          ConstOverheadCompile.Main.gridGates ((2 ^ (0 : ℕ)) ^ r)) n),
      A.maxGates ≤ G →
      ∃ (a : ℕ) (A' : ConstOverheadCompile.Main.AdaptiveCircuit
          ConstOverheadCompile.Main.CliffordT (n + a)),
        (A'.maxGates : ℝ) ≤ (G : ℝ) ∧
        ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef ε) ∧
    (∀ (r b : ℕ) (ε : ℝ), 0 < ε → ∀ (n : ℕ)
      (A : ConstOverheadCompile.Main.AdaptiveCircuit
        (ConstOverheadCompile.Main.CliffordT ∪
          ConstOverheadCompile.Main.gridGates ((2 ^ b) ^ r)) n),
      A.maxGates ≤ 0 →
      ∃ (a : ℕ) (A' : ConstOverheadCompile.Main.AdaptiveCircuit
          ConstOverheadCompile.Main.CliffordT (n + a)),
        (A'.maxGates : ℝ) ≤ 0 ∧
        ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef ε) ∧
    (∀ (r b : ℕ), 2 ≤ r → 1 ≤ b → ∀ (m_cut n G : ℕ)
      (A : ConstOverheadCompile.Main.AdaptiveCircuit
        (ConstOverheadCompile.Main.CliffordT ∪
          ConstOverheadCompile.Main.gridGates ((2 ^ b) ^ r)) n),
      A.maxGates ≤ G →
      let L : ℕ := 2 * (2 ^ b * (b * r))
      let M : ℕ := b * r
      ∃ (α : Fin L → ℝ)
        (B_circ : ConstOverheadCompile.Main.AdaptiveCircuit
          ConstOverheadCompile.Main.CliffordT (n + (L + M))),
        (B_circ.maxGates : ℝ) ≤ (G : ℝ) + 200 * (m_cut : ℝ) ∧
        ∀ (m_ref : ℕ)
          (ρ : Matrix (Fin m_ref × QAlgorithms.Qubits n) (Fin m_ref × QAlgorithms.Qubits n) ℂ),
          WildeQIT.IsDensityOperator ρ →
          WildeQIT.traceDist
            (t9_partialTraceAnc
              (B_circ.channelRef m_ref (t9_tensorAncVec (t9_productAncVec α) ρ)))
            (A.channelRef m_ref ρ) ≤
            2 * ((∑ k ∈ Finset.range (r * G), (m_cut.choose k : ℝ)) / 2 ^ m_cut))

def Thm9Step4Type : Prop :=
  ∀ (C_RS ε₀ : ℝ), 0 < C_RS → 0 < ε₀ →
    ∃ C₀ : ℝ,
      (∀ (r : ℕ), 2 ≤ r → ∀ (ε : ℝ) (G : ℕ),
        (G : ℝ) ≤ C₀ * ((r : ℝ) * (G : ℝ) +
          (r : ℝ) * (2 : ℝ) ^ (0 : ℕ) * Real.log ((2 : ℝ) ^ (0 : ℕ)) *
            Real.log (ε⁻¹ * (2 : ℝ) ^ (0 : ℕ) * (r : ℝ) * Real.log ((2 : ℝ) ^ (0 : ℕ))))) ∧
      (∀ (r b : ℕ), 2 ≤ r → 1 ≤ b → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        (0 : ℝ) ≤ C₀ * ((r : ℝ) * ((0 : ℕ) : ℝ) +
          (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
            Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)))) ∧
      (∀ (r b : ℕ), 2 ≤ r → 1 ≤ b → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ (G : ℕ), 1 ≤ G →
          let L : ℕ := 2 * (2 ^ b * (b * r))
          ∃ (m_cut : ℕ) (δ_tot : ℝ),
            0 < δ_tot ∧
            2 * δ_tot + 2 * ((∑ k ∈ Finset.range (r * G), (m_cut.choose k : ℝ)) / 2 ^ m_cut) ≤ ε ∧
            (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) +
              (G : ℝ) + 200 * (m_cut : ℝ) ≤
              C₀ * ((r : ℝ) * (G : ℝ) +
                (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
                  Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b))))

theorem t9_master_glue_check
    (s1 : Thm9Step1API) (s2 : Thm9Step2API) (s3 : Thm9Step3Type) (s4 : Thm9Step4Type) :
    ∃ C₀ : ℝ, ∀ r b : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (n G : ℕ)
        (A : ConstOverheadCompile.Main.AdaptiveCircuit
          (ConstOverheadCompile.Main.CliffordT ∪ ConstOverheadCompile.Main.gridGates ((2 ^ b) ^ r)) n),
        A.maxGates ≤ G →
        ∃ (a : ℕ)
          (A' : ConstOverheadCompile.Main.AdaptiveCircuit ConstOverheadCompile.Main.CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C₀ * ((r : ℝ) * G + (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
              Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b))) ∧
          ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef ε := by
  obtain ⟨C_RS, ε₀, hC_RS, hε₀, hRS⟩ := ConstOverheadCompile.Main.ross_selinger_synthesis
  obtain ⟨C₀, hB0_bound, hG0_bound, hMain_bound⟩ := s4 C_RS ε₀ hC_RS hε₀
  obtain ⟨hStep3_b0, hStep3_G0, hStep3_main⟩ := s3 s1 s2
  refine ⟨C₀, fun r b hr ε hε0 hε1 n G A hAG => ?_⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb_pos
  · obtain ⟨a, A', hGates, hClose⟩ := hStep3_b0 r hr ε hε0 n G A hAG
    exact ⟨a, A', le_trans hGates (hB0_bound r hr ε G), hClose⟩
  · rcases Nat.eq_zero_or_pos G with rfl | hG_pos
    · obtain ⟨a, A', hGates, hClose⟩ := hStep3_G0 r b ε hε0 n A hAG
      exact ⟨a, A', le_trans hGates (hG0_bound r b hr hb_pos ε hε0 hε1), hClose⟩
    · let L : ℕ := 2 * (2 ^ b * (b * r))
      let M : ℕ := b * r
      have hL_pos : 1 ≤ L := by
        have h2b : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by norm_num)
        have hbr : 1 ≤ b * r := Nat.mul_pos hb_pos (by omega)
        dsimp [L]; nlinarith
      obtain ⟨m_cut, δ_tot, hδ_pos, hErr_sum, hGate_sum⟩ :=
        hMain_bound r b hr hb_pos ε hε0 hε1 G hG_pos
      obtain ⟨α, B_circ, hB_gates, hB_close⟩ :=
        hStep3_main r b hr hb_pos m_cut n G A hAG
      obtain ⟨cPrep, Φ, hcPrep_size, hχ_app, hχ_id, hχ_dist⟩ :=
        s1.prep_resource_states hC_RS hε₀ hRS L M hL_pos α hδ_pos
      let A' := t9_prependCircuit (t9_liftAncCircuit n cPrep) B_circ
      refine ⟨L + M, A', ?_, ?_⟩
      · have hmax : (A'.maxGates : ℝ) = (cPrep.size : ℝ) + (B_circ.maxGates : ℝ) := by
          dsimp [A']
          rw [t9_prependCircuit_maxGates, t9_liftAncCircuit_size]
          push_cast; ring
        rw [hmax]
        linarith
      · intro m_ref ρ hρ
        rw [s1.prependAnc_dataChannelRef]
        have h1 : WildeQIT.traceDist
            (t9_partialTraceAnc (B_circ.channelRef m_ref
              (t9_tensorAncVec (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) ρ)))
            (t9_partialTraceAnc (B_circ.channelRef m_ref
              (t9_tensorAncVec (t9_productAncVec α) ρ))) ≤ 2 * δ_tot :=
          s1.channelWithAnc_approx_le s1.cliffordT_isUnitary B_circ hχ_app hχ_id
            (le_of_lt hδ_pos) Φ hχ_dist m_ref hρ
        have h2 := hB_close m_ref ρ hρ
        have hHerm1 : (t9_partialTraceAnc (B_circ.channelRef m_ref
            (t9_tensorAncVec (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) ρ))).IsHermitian :=
          s1.isHermitian_partialTraceAnc
            (s1.isHermitian_channelRef B_circ
              (s1.isDensityOperator_tensorAncVec hχ_app hρ).1.isHermitian)
        have hHerm2 : (t9_partialTraceAnc (B_circ.channelRef m_ref
            (t9_tensorAncVec (t9_productAncVec α) ρ))).IsHermitian :=
          s1.isHermitian_partialTraceAnc
            (s1.isHermitian_channelRef B_circ
              (s1.isDensityOperator_tensorAncVec hχ_id hρ).1.isHermitian)
        have hHerm3 : (A.channelRef m_ref ρ).IsHermitian :=
          s1.isHermitian_channelRef A hρ.1.isHermitian
        have htri := s1.traceDist_triangle hHerm1 hHerm2 hHerm3
        linarith

end Thm9SharedDefs

section Thm9Step1Helpers

open QAlgorithms ConstOverheadCompile.Main

/-! ### Part 1: Hermitian Trace-Norm, Trace-Distance, and CPTP Helpers -/

private lemma t9s1_unitary_mul_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

private lemma t9s1_unitary_conjTranspose_mul {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

private lemma t9s1_unitary_conjTranspose_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  exact t9s1_unitary_conjTranspose_mul hU

private lemma t9s1_trace_conj_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) (D : Matrix ι ι ℂ) :
    (U * D * Uᴴ).trace = D.trace := by
  rw [Matrix.trace_mul_cycle, t9s1_unitary_conjTranspose_mul hU, one_mul]

private lemma t9s1_hermitian_spectral {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) *
      (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
  conv_lhs => rw [hX.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

private lemma t9s1_conj_diag_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (s : ι → ℂ)
    (hs : ∀ i, s i * star (s i) = 1) :
    U * Matrix.diagonal s * Uᴴ ∈ Matrix.unitaryGroup ι ℂ := by
  have hs_diag : Matrix.diagonal s * (Matrix.diagonal s)ᴴ = 1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    simp only [Pi.star_apply, hs i]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (U * Matrix.diagonal s * Uᴴ) * (U * ((Matrix.diagonal s)ᴴ * Uᴴ))
      = U * (Matrix.diagonal s * (Uᴴ * U) * (Matrix.diagonal s)ᴴ) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal s * (Matrix.diagonal s)ᴴ) * Uᴴ := by
          rw [t9s1_unitary_conjTranspose_mul hU, Matrix.mul_one]
    _ = U * Uᴴ := by rw [hs_diag, Matrix.mul_one]
    _ = 1 := t9s1_unitary_mul_conjTranspose hU

private lemma t9s1_conj_diag_mul_conj_diag {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (d₁ d₂ : ι → ℂ) :
    (U * Matrix.diagonal d₁ * Uᴴ) * (U * Matrix.diagonal d₂ * Uᴴ) =
      U * Matrix.diagonal (fun i => d₁ i * d₂ i) * Uᴴ := by
  calc (U * Matrix.diagonal d₁ * Uᴴ) * (U * Matrix.diagonal d₂ * Uᴴ)
      = U * (Matrix.diagonal d₁ * (Uᴴ * U) * Matrix.diagonal d₂) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = U * (Matrix.diagonal d₁ * Matrix.diagonal d₂) * Uᴴ := by
          rw [t9s1_unitary_conjTranspose_mul hU, Matrix.mul_one]
    _ = U * Matrix.diagonal (fun i => d₁ i * d₂ i) * Uᴴ := by
          rw [Matrix.diagonal_mul_diagonal]

private lemma t9s1_traceNorm_eq_sum_abs_eigenvalues {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm X = ∑ i : ι, |hX.eigenvalues i| := by
  have h1 : CFC.sqrt (Xᴴ * X) = CFC.abs X := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  have h2 : CFC.abs X = cfc (fun r : ℝ => ‖r‖) X :=
    CFC.abs_eq_cfc_norm X (Matrix.isHermitian_iff_isSelfAdjoint.mp hX)
  have h3 : cfc (fun r : ℝ => ‖r‖) X = hX.cfc (fun r : ℝ => ‖r‖) :=
    Matrix.IsHermitian.cfc_eq hX _
  have h4 : (hX.cfc (fun r : ℝ => ‖r‖)).trace = ∑ i : ι, ((|hX.eigenvalues i| : ℝ) : ℂ) := by
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rw [t9s1_trace_conj_unitary hX.eigenvectorUnitary.prop, Matrix.trace_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp_apply, Real.norm_eq_abs]
    rfl
  unfold WildeQIT.traceNorm
  rw [h1, h2, h3, h4, Complex.re_sum]
  simp only [Complex.ofReal_re]

private lemma t9s1_traceNorm_eq_trace_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ∃ S ∈ Matrix.unitaryGroup ι ℂ, WildeQIT.traceNorm X = (Matrix.trace (S * X)).re := by
  let s : ι → ℂ := fun i => if 0 ≤ hX.eigenvalues i then 1 else -1
  let U : Matrix ι ι ℂ := hX.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hX.eigenvectorUnitary.prop
  have hS : U * Matrix.diagonal s * Uᴴ ∈ Matrix.unitaryGroup ι ℂ :=
    t9s1_conj_diag_unitary U hU s fun i => by dsimp [s]; split_ifs <;> simp
  refine ⟨U * Matrix.diagonal s * Uᴴ, hS, ?_⟩
  have hdiag : (fun i => s i * (hX.eigenvalues i : ℂ)) =
      (fun i => ((|hX.eigenvalues i| : ℝ) : ℂ)) := by
    ext i
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; push_cast; ring
  have hSX : (U * Matrix.diagonal s * Uᴴ) * X =
      U * Matrix.diagonal (fun i => ((|hX.eigenvalues i| : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rhs; rw [t9s1_hermitian_spectral hX]
    rw [t9s1_conj_diag_mul_conj_diag U hU s (fun i => (hX.eigenvalues i : ℂ)), hdiag]
  rw [hSX, t9s1_trace_conj_unitary hU, Matrix.trace_diagonal,
    t9s1_traceNorm_eq_sum_abs_eigenvalues hX, Complex.re_sum]
  simp only [Complex.ofReal_re]

private lemma t9s1_unitary_entry_norm_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) (i j : ι) :
    ‖W i j‖ ≤ 1 := by
  have h1 : (Wᴴ * W) j j = 1 := by
    rw [t9s1_unitary_conjTranspose_mul hW, Matrix.one_apply_eq]
  have h2 : ∑ k : ι, ‖W k j‖ ^ 2 = 1 := by
    have h1' : (∑ k : ι, star (W k j) * W k j).re = (1 : ℂ).re := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congrArg Complex.re h1
    simp only [Complex.one_re] at h1'
    rw [← h1', Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmul : star (W k j) * W k j = ((‖W k j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul, Complex.ofReal_re]
  have hsq : ‖W i j‖ ^ 2 ≤ 1 := by
    calc ‖W i j‖ ^ 2 ≤ ∑ k : ι, ‖W k j‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖W k j‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      _ = 1 := h2
  nlinarith [norm_nonneg (W i j)]

private lemma t9s1_norm_trace_unitary_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    ‖Matrix.trace (W * X)‖ ≤ WildeQIT.traceNorm X := by
  let U : Matrix ι ι ℂ := hX.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup ι ℂ := hX.eigenvectorUnitary.prop
  let W' : Matrix ι ι ℂ := Uᴴ * W * U
  have hW' : W' ∈ Matrix.unitaryGroup ι ℂ :=
    mul_mem (mul_mem (t9s1_unitary_conjTranspose_mem hU) hW) hU
  have htr : Matrix.trace (W * X) =
      ∑ i : ι, W' i i * (hX.eigenvalues i : ℂ) := by
    calc Matrix.trace (W * X)
        = Matrix.trace (W * (U * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ)) := by
            conv_lhs => rw [t9s1_hermitian_spectral hX]
      _ = Matrix.trace ((W * U) * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) * Uᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Uᴴ * (W * U) * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) := by
            rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace (W' * Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ))) := by
            simp only [W', Matrix.mul_assoc]
      _ = ∑ i : ι, W' i i * (hX.eigenvalues i : ℂ) := by
            simp [Matrix.trace, Matrix.mul_diagonal]
  rw [htr, t9s1_traceNorm_eq_sum_abs_eigenvalues hX]
  calc ‖∑ i : ι, W' i i * (hX.eigenvalues i : ℂ)‖
      ≤ ∑ i : ι, ‖W' i i * (hX.eigenvalues i : ℂ)‖ := norm_sum_le _ _
    _ = ∑ i : ι, ‖W' i i‖ * |hX.eigenvalues i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ i : ι, 1 * |hX.eigenvalues i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (t9s1_unitary_entry_norm_le_one hW' i i) (abs_nonneg _)
    _ = ∑ i : ι, |hX.eigenvalues i| := by simp

private lemma t9s1_re_trace_unitary_mul_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {W : Matrix ι ι ℂ} (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (Matrix.trace (W * X)).re ≤ WildeQIT.traceNorm X :=
  (Complex.re_le_norm _).trans (t9s1_norm_trace_unitary_mul_le hX hW)

private lemma t9s1_traceNorm_neg {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    WildeQIT.traceNorm (-A) = WildeQIT.traceNorm A := by
  simp [WildeQIT.traceNorm]

private lemma t9s1_traceNorm_of_posSemidef {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    WildeQIT.traceNorm A = A.trace.re := by
  have h1 : CFC.sqrt (Aᴴ * A) = CFC.abs A := by
    rw [← Matrix.star_eq_conjTranspose]
    rfl
  unfold WildeQIT.traceNorm
  rw [h1, CFC.abs_of_nonneg A hA.nonneg]

private lemma t9s1_posSemidef_list_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {l : List (Matrix ι ι ℂ)} (hl : ∀ M ∈ l, M.PosSemidef) :
    l.sum.PosSemidef := by
  induction l with
  | nil => simpa using Matrix.PosSemidef.zero
  | cons M ms ih =>
      simp only [List.sum_cons]
      exact (hl M (by simp)).add (ih fun N hN => hl N (by simp [hN]))

private lemma t9s1_list_map_kraus_sub {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix κ ι ℂ)) (A B : Matrix ι ι ℂ) :
    (ks.map fun K => K * (A - B) * Kᴴ).sum =
      (ks.map fun K => K * A * Kᴴ).sum - (ks.map fun K => K * B * Kᴴ).sum := by
  induction ks with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      abel

private lemma t9s1_trace_list_map_kraus {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix κ ι ℂ)) (A : Matrix ι ι ℂ) :
    (ks.map fun K => K * A * Kᴴ).sum.trace =
      ((ks.map fun K => Kᴴ * K).sum * A).trace := by
  induction ks with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons, Matrix.trace_add, Matrix.add_mul, ih]
      congr 1
      rw [Matrix.trace_mul_cycle]

private lemma t9s1_trace_mul_conjTranspose_self_re {κ ι : Type} [Fintype κ] [Fintype ι]
    (M : Matrix κ ι ℂ) :
    (Matrix.trace (M * Mᴴ)).re = ∑ p : κ × ι, ‖M p.1 p.2‖ ^ 2 := by
  have htr : (Matrix.trace (M * Mᴴ)).re = ∑ i : κ, ∑ j : ι, ‖M i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hmul : M i j * star (M i j) = ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    rw [hmul, Complex.ofReal_re]
  rw [htr, Fintype.sum_prod_type]

private lemma t9s1_frobenius_cauchy_schwarz {κ ι : Type} [Fintype κ] [Fintype ι]
    (P Q : Matrix κ ι ℂ) :
    ‖Matrix.trace (P * Qᴴ)‖ ≤
      Real.sqrt (Matrix.trace (P * Pᴴ)).re * Real.sqrt (Matrix.trace (Q * Qᴴ)).re := by
  rw [t9s1_trace_mul_conjTranspose_self_re P, t9s1_trace_mul_conjTranspose_self_re Q]
  calc ‖Matrix.trace (P * Qᴴ)‖
      = ‖∑ i : κ, ∑ j : ι, P i j * star (Q i j)‖ := by
          simp [Matrix.trace, Matrix.mul_apply]
    _ = ‖∑ p : κ × ι, P p.1 p.2 * star (Q p.1 p.2)‖ := by
          rw [Fintype.sum_prod_type]
    _ ≤ ∑ p : κ × ι, ‖P p.1 p.2 * star (Q p.1 p.2)‖ := norm_sum_le _ _
    _ = ∑ p : κ × ι, ‖P p.1 p.2‖ * ‖Q p.1 p.2‖ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ p : κ × ι, ‖P p.1 p.2‖ ^ 2) *
          Real.sqrt (∑ p : κ × ι, ‖Q p.1 p.2‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _

private lemma t9s1_trace_unitary_mul_frobenius {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι]
    {S : Matrix κ κ ℂ} (hS : S ∈ Matrix.unitaryGroup κ ℂ) (M : Matrix κ ι ℂ) :
    (Matrix.trace ((S * M) * (S * M)ᴴ)).re = (Matrix.trace (M * Mᴴ)).re := by
  have h1 : Matrix.trace ((S * M) * (S * M)ᴴ) = Matrix.trace ((S * M)ᴴ * (S * M)) :=
    Matrix.trace_mul_comm _ _
  have h2 : (S * M)ᴴ * (S * M) = Mᴴ * M := by
    calc (S * M)ᴴ * (S * M)
        = Mᴴ * (Sᴴ * S) * M := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * M := by rw [t9s1_unitary_conjTranspose_mul hS, Matrix.mul_one]
  have h3 : Matrix.trace (Mᴴ * M) = Matrix.trace (M * Mᴴ) := Matrix.trace_mul_comm _ _
  rw [h1, h2, h3]

private lemma t9s1_normalize_psd_density {ι : Type} [Fintype ι]
    {M ρ₀ : Matrix ι ι ℂ} (hM : M.PosSemidef) (hρ₀ : WildeQIT.IsDensityOperator ρ₀) :
    0 ≤ M.trace.re ∧
      ∃ σ : Matrix ι ι ℂ, WildeQIT.IsDensityOperator σ ∧ M = (M.trace.re : ℂ) • σ := by
  have htr_nonneg : 0 ≤ M.trace := hM.trace_nonneg
  have hre_nonneg : 0 ≤ M.trace.re := (Complex.nonneg_iff.mp htr_nonneg).1
  have him_zero : M.trace.im = 0 := (Complex.nonneg_iff.mp htr_nonneg).2.symm
  have htr_coe : (M.trace.re : ℂ) = M.trace := Complex.ext rfl him_zero.symm
  refine ⟨hre_nonneg, ?_⟩
  by_cases hp : M.trace.re = 0
  · refine ⟨ρ₀, hρ₀, ?_⟩
    have htr0 : M.trace = 0 := by rw [← htr_coe, hp]; simp
    have hM0 : M = 0 := hM.trace_eq_zero_iff.mp htr0
    rw [hp]
    simp [hM0]
  · refine ⟨((M.trace.re⁻¹ : ℝ) : ℂ) • M, ?_, ?_⟩
    · refine ⟨hM.smul (Complex.nonneg_iff.mpr ⟨by simpa using inv_nonneg.mpr hre_nonneg, by simp⟩), ?_⟩
      rw [Matrix.trace_smul, smul_eq_mul, ← htr_coe]
      norm_cast
      exact inv_mul_cancel₀ hp
    · rw [smul_smul]
      have hmul : (M.trace.re : ℂ) * ((M.trace.re⁻¹ : ℝ) : ℂ) = 1 := by
        norm_cast
        exact mul_inv_cancel₀ hp
      rw [hmul, one_smul]

private theorem t9s1_traceDist_self {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    WildeQIT.traceDist A A = 0 := by
  simp [WildeQIT.traceDist, WildeQIT.traceNorm]

private theorem t9s1_traceNorm_add_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    WildeQIT.traceNorm (X + Y) ≤ WildeQIT.traceNorm X + WildeQIT.traceNorm Y := by
  obtain ⟨S, hS, hnorm⟩ := t9s1_traceNorm_eq_trace_unitary (hX.add hY)
  rw [hnorm, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  exact add_le_add (t9s1_re_trace_unitary_mul_le hX hS) (t9s1_re_trace_unitary_mul_le hY hS)

private theorem t9s1_traceDist_triangle {ι : Type} [Fintype ι] [DecidableEq ι]
    {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    WildeQIT.traceDist A C ≤ WildeQIT.traceDist A B + WildeQIT.traceDist B C := by
  unfold WildeQIT.traceDist
  have hsub : A - C = (A - B) + (B - C) := by abel
  rw [hsub]
  exact t9s1_traceNorm_add_le (hA.sub hB) (hB.sub hC)

private theorem t9s1_traceNorm_smul_of_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {c : ℝ} (hc : 0 ≤ c) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm ((c : ℂ) • X) = c * WildeQIT.traceNorm X := by
  have hcX : ((c : ℂ) • X).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX.eq]
  apply le_antisymm
  · obtain ⟨S, hS, hnorm⟩ := t9s1_traceNorm_eq_trace_unitary hcX
    rw [hnorm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (t9s1_re_trace_unitary_mul_le hX hS) hc
  · obtain ⟨S, hS, hnorm⟩ := t9s1_traceNorm_eq_trace_unitary hX
    rw [hnorm]
    calc c * (Matrix.trace (S * X)).re
        = (Matrix.trace (S * ((c : ℂ) • X))).re := by
            rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
      _ ≤ WildeQIT.traceNorm ((c : ℂ) • X) := t9s1_re_trace_unitary_mul_le hcX hS

private theorem t9s1_isDensityOperator_conj_unitary {ι : Type} [Fintype ι] [DecidableEq ι]
    {ρ U : Matrix ι ι ℂ} (hρ : WildeQIT.IsDensityOperator ρ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    WildeQIT.IsDensityOperator (U * ρ * Uᴴ) := by
  refine ⟨hρ.1.mul_mul_conjTranspose_same U, ?_⟩
  rw [t9s1_trace_conj_unitary hU, hρ.2]

private theorem t9s1_cptp_traceNorm_le_rect {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix κ ι ℂ)) (hks : (ks.map fun K => Kᴴ * K).sum = 1)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm ((ks.map fun K => K * X * Kᴴ).sum) ≤ WildeQIT.traceNorm X := by
  have hXsa : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  let Xp : Matrix ι ι ℂ := X⁺
  let Xm : Matrix ι ι ℂ := X⁻
  have hXp : Xp.PosSemidef := Matrix.LE.le.posSemidef (CFC.posPart_nonneg X)
  have hXm : Xm.PosSemidef := Matrix.LE.le.posSemidef (CFC.negPart_nonneg X)
  have hsub : Xp - Xm = X := CFC.posPart_sub_negPart X hXsa
  have hadd : Xp + Xm = CFC.abs X := CFC.posPart_add_negPart X hXsa
  let Yp : Matrix κ κ ℂ := (ks.map fun K => K * Xp * Kᴴ).sum
  let Ym : Matrix κ κ ℂ := (ks.map fun K => K * Xm * Kᴴ).sum
  have hYp : Yp.PosSemidef := t9s1_posSemidef_list_sum fun M hM => by
    rcases List.mem_map.mp hM with ⟨K, _, rfl⟩
    exact hXp.mul_mul_conjTranspose_same K
  have hYm : Ym.PosSemidef := t9s1_posSemidef_list_sum fun M hM => by
    rcases List.mem_map.mp hM with ⟨K, _, rfl⟩
    exact hXm.mul_mul_conjTranspose_same K
  have hsum : (ks.map fun K => K * X * Kᴴ).sum = Yp + (-Ym) := by
    rw [← hsub, t9s1_list_map_kraus_sub, sub_eq_add_neg]
  have htr_p : Yp.trace = Xp.trace := by
    dsimp [Yp]
    rw [t9s1_trace_list_map_kraus, hks, one_mul]
  have htr_m : Ym.trace = Xm.trace := by
    dsimp [Ym]
    rw [t9s1_trace_list_map_kraus, hks, one_mul]
  have hX_norm : WildeQIT.traceNorm X = Xp.trace.re + Xm.trace.re := by
    have h1 : CFC.sqrt (Xᴴ * X) = CFC.abs X := by
      rw [← Matrix.star_eq_conjTranspose]
      rfl
    unfold WildeQIT.traceNorm
    rw [h1, ← hadd, Matrix.trace_add, Complex.add_re]
  rw [hsum]
  calc WildeQIT.traceNorm (Yp + -Ym)
      ≤ WildeQIT.traceNorm Yp + WildeQIT.traceNorm (-Ym) :=
          t9s1_traceNorm_add_le hYp.isHermitian hYm.isHermitian.neg
    _ = WildeQIT.traceNorm Yp + WildeQIT.traceNorm Ym := by
          rw [t9s1_traceNorm_neg]
    _ = Yp.trace.re + Ym.trace.re := by
          rw [t9s1_traceNorm_of_posSemidef hYp, t9s1_traceNorm_of_posSemidef hYm]
    _ = Xp.trace.re + Xm.trace.re := by rw [htr_p, htr_m]
    _ = WildeQIT.traceNorm X := hX_norm.symm

private theorem t9s1_cptp_traceNorm_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (ks : List (Matrix ι ι ℂ)) (hks : (ks.map fun K => Kᴴ * K).sum = 1)
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    WildeQIT.traceNorm ((ks.map fun K => K * X * Kᴴ).sum) ≤ WildeQIT.traceNorm X :=
  t9s1_cptp_traceNorm_le_rect ks hks hX

private theorem t9s1_proj_decomp_density {m n : ℕ} (q : Fin n)
    {ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ}
    (hρ : WildeQIT.IsDensityOperator ρ) :
    ∃ (pf pt : ℝ)
      (ρf ρt : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ),
      0 ≤ pf ∧ 0 ≤ pt ∧ pf + pt = 1 ∧
      WildeQIT.IsDensityOperator ρf ∧ WildeQIT.IsDensityOperator ρt ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false)ᴴ =
        (pf : ℂ) • ρf ∧
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true) * ρ *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true)ᴴ =
        (pt : ℂ) • ρt := by
  let Pf := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false
  let Pt := (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true
  let Mf := Pf * ρ * Pfᴴ
  let Mt := Pt * ρ * Ptᴴ
  have hMf : Mf.PosSemidef := hρ.1.mul_mul_conjTranspose_same Pf
  have hMt : Mt.PosSemidef := hρ.1.mul_mul_conjTranspose_same Pt
  obtain ⟨hpf, ρf, hρf, hMf_eq⟩ := t9s1_normalize_psd_density hMf hρ
  obtain ⟨hpt, ρt, hρt, hMt_eq⟩ := t9s1_normalize_psd_density hMt hρ
  have hproj_herm : ∀ b : Bool,
      (AdaptiveCircuit.proj q b)ᴴ = AdaptiveCircuit.proj q b := by
    intro b
    unfold AdaptiveCircuit.proj
    rw [Matrix.diagonal_conjTranspose]
    congr 1; ext x
    by_cases h : x q = b <;> simp [h]
  have hproj_idem : ∀ b : Bool,
      AdaptiveCircuit.proj q b * AdaptiveCircuit.proj q b = AdaptiveCircuit.proj q b := by
    intro b
    unfold AdaptiveCircuit.proj
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; ext x
    by_cases h : x q = b <;> simp [h]
  have hproj_sum : AdaptiveCircuit.proj q false + AdaptiveCircuit.proj q true = 1 := by
    unfold AdaptiveCircuit.proj
    rw [Matrix.diagonal_add, ← Matrix.diagonal_one]
    congr 1; ext x
    cases x q <;> simp
  have hPf_sq : Pfᴴ * Pf = Pf := by
    dsimp [Pf]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hproj_herm,
      ← Matrix.mul_kronecker_mul, one_mul, hproj_idem]
  have hPt_sq : Ptᴴ * Pt = Pt := by
    dsimp [Pt]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, hproj_herm,
      ← Matrix.mul_kronecker_mul, one_mul, hproj_idem]
  have hsum_id : Pfᴴ * Pf + Ptᴴ * Pt = 1 := by
    rw [hPf_sq, hPt_sq]
    dsimp [Pf, Pt]
    rw [← Matrix.kronecker_add, hproj_sum, Matrix.one_kronecker_one]
  have htr_sum : Mf.trace.re + Mt.trace.re = 1 := by
    have htrC : Mf.trace + Mt.trace = 1 := by
      dsimp [Mf, Mt]
      rw [Matrix.trace_mul_cycle Pf ρ Pfᴴ, Matrix.trace_mul_cycle Pt ρ Ptᴴ,
        ← Matrix.trace_add, ← Matrix.add_mul, hsum_id, one_mul, hρ.2]
    simpa [Complex.add_re] using congrArg Complex.re htrC
  exact ⟨Mf.trace.re, Mt.trace.re, ρf, ρt, hpf, hpt, htr_sum, hρf, hρt, hMf_eq, hMt_eq⟩

private theorem t9s1_traceDist_density_le_two {ι : Type} [Fintype ι] [DecidableEq ι]
    {σ₁ σ₂ : Matrix ι ι ℂ}
    (hσ₁ : WildeQIT.IsDensityOperator σ₁) (hσ₂ : WildeQIT.IsDensityOperator σ₂) :
    WildeQIT.traceDist σ₁ σ₂ ≤ 2 := by
  unfold WildeQIT.traceDist
  rw [sub_eq_add_neg]
  calc WildeQIT.traceNorm (σ₁ + -σ₂)
      ≤ WildeQIT.traceNorm σ₁ + WildeQIT.traceNorm (-σ₂) :=
          t9s1_traceNorm_add_le hσ₁.1.isHermitian hσ₂.1.isHermitian.neg
    _ = WildeQIT.traceNorm σ₁ + WildeQIT.traceNorm σ₂ := by
          rw [t9s1_traceNorm_neg]
    _ = σ₁.trace.re + σ₂.trace.re := by
          rw [t9s1_traceNorm_of_posSemidef hσ₁.1, t9s1_traceNorm_of_posSemidef hσ₂.1]
    _ = 1 + 1 := by rw [hσ₁.2, hσ₂.2, Complex.one_re]
    _ = 2 := by norm_num

/-! ### Part 2: Gates, Unitarity, and Circuit Lifting Helpers -/

private theorem t9s1_ofMatrix1_isUnitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    (Gate.ofMatrix1 M).IsUnitary := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.mem_unitaryGroup_iff] at hM
  change M * Mᴴ = 1 at hM
  let e : Qubits 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun b _ => b
      left_inv := fun b => funext fun i => by rw [Fin.eq_zero i]
      right_inv := fun _ => rfl }
  change (M.submatrix e e) * (M.submatrix e e)ᴴ = 1
  have hsub : (M.submatrix e e)ᴴ = Mᴴ.submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv M Mᴴ e e e, hM, Matrix.submatrix_one_equiv]

private theorem t9s1_ofMatrix2_isUnitary {M : Matrix (Bool × Bool) (Bool × Bool) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) :
    (Gate.ofMatrix2 M).IsUnitary := by
  dsimp [Gate.IsUnitary, Gate.ofMatrix2]
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.mem_unitaryGroup_iff] at hM
  change M * Mᴴ = 1 at hM
  let e : Qubits 2 ≃ Bool × Bool :=
    { toFun := fun b => (b 0, b 1)
      invFun := fun p i => if i = 0 then p.1 else p.2
      left_inv := fun b => funext fun i => by fin_cases i <;> rfl
      right_inv := fun p => by simp }
  change (M.submatrix e e) * (M.submatrix e e)ᴴ = 1
  have hsub : (M.submatrix e e)ᴴ = Mᴴ.submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv M Mᴴ e e e, hM, Matrix.submatrix_one_equiv]

private theorem t9s1_hadamard_mem_unitary : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change hadamard * hadamardᴴ = 1
  have hH : hadamardᴴ = hadamard := by
    ext a b
    cases a <;> cases b <;> simp [hadamard, Matrix.conjTranspose_apply, Complex.conj_ofReal]
  rw [hH, hadamard_mul_self]

private theorem t9s1_gateT_mem_unitary : gateT ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change gateT * gateTᴴ = 1
  have hT : gateTᴴ = Matrix.diagonal (fun a => if a then star (Complex.exp (Complex.I * Real.pi / 4)) else 1) := by
    ext x y
    simp only [gateT, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simp; split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hT, gateT, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    cases a
    · simp
    · simp only [↓reduceIte, Complex.star_def]
      have harg : Complex.I * (Real.pi : ℂ) / 4 = ((Real.pi / 4 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
        Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]
  · simp [h]

private theorem t9s1_cnot_mem_unitary : cnot ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change cnot * cnotᴴ = 1
  have hC : cnotᴴ = cnot := by
    ext p q
    simp only [cnot, Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases hpq : p.1 = q.1 ∧ p.2 = xor q.2 q.1
    · have hqp : q.1 = p.1 ∧ q.2 = xor p.2 p.1 := by
        refine ⟨hpq.1.symm, ?_⟩
        rw [hpq.1, hpq.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rw [if_pos hpq, if_pos hqp, star_one]
    · have hqp : ¬ (q.1 = p.1 ∧ q.2 = xor p.2 p.1) := by
        intro h
        apply hpq
        refine ⟨h.1.symm, ?_⟩
        rw [h.1, h.2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      rw [if_neg hpq, if_neg hqp, star_zero]
  rw [hC]
  ext p q
  rcases p with ⟨p1, p2⟩; rcases q with ⟨q1, q2⟩
  simp only [cnot, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Fintype.sum_bool]
  cases p1 <;> cases p2 <;> cases q1 <;> cases q2 <;> norm_num

private theorem t9s1_rot_mem_unitary (θ : ℝ) : rot θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change rot θ * (rot θ)ᴴ = 1
  have hdiag : (rot θ)ᴴ = Matrix.diagonal (fun x => if x then star (Complex.exp ((θ : ℂ) * Complex.I)) else 1) := by
    ext x y
    simp only [rot, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simp; split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hdiag, rot, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    cases a
    · simp
    · simp only [↓reduceIte, Complex.star_def]
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
        Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]
  · simp [h]

private theorem t9s1_cliffordT_isUnitary : ∀ g ∈ CliffordT, g.IsUnitary := by
  intro g hg
  rcases hg with rfl | rfl | rfl
  · exact t9s1_ofMatrix1_isUnitary t9s1_hadamard_mem_unitary
  · exact t9s1_ofMatrix1_isUnitary t9s1_gateT_mem_unitary
  · exact t9s1_ofMatrix2_isUnitary t9s1_cnot_mem_unitary

private theorem t9s1_embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

private theorem t9s1_embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

private theorem t9s1_embedOp_conjTranspose {m n : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp Mᴴ w = (embedOp M w)ᴴ := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h), star_zero]

private theorem t9s1_embedOp_isUnitary {m n : ℕ} {M : Matrix (Qubits m) (Qubits m) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits m) ℂ) (w : Fin m ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  change M * Mᴴ = 1 at hM
  change embedOp M w * (embedOp M w)ᴴ = 1
  rw [← t9s1_embedOp_conjTranspose, ← t9s1_embedOp_mul, hM, embedOp_one]

private theorem t9s1_unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := rfl

private theorem t9s1_unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (cs : Circuit S n) :
    Circuit.unitary (g :: cs) = Circuit.unitary cs * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

private theorem t9s1_unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  induction c₁ with
  | nil => simp [t9s1_unitary_nil]
  | cons g gs ih =>
      rw [List.cons_append, t9s1_unitary_cons, ih, t9s1_unitary_cons, Matrix.mul_assoc]

private theorem t9s1_circuit_unitary_mem_unitary {S : Set Gate}
    (hS : ∀ g ∈ S, g.IsUnitary) {n : ℕ} (c : Circuit S n) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction c with
  | nil => rw [t9s1_unitary_nil]; exact one_mem _
  | cons g cs ih =>
      rw [t9s1_unitary_cons]
      exact mul_mem ih (t9s1_embedOp_isUnitary (hS g.gate g.mem) g.wires)

private theorem t9s1_liftCircuit_unitary {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) :
    Circuit.unitary (c.map fun g => (⟨g.gate, g.mem, g.wires.trans w⟩ : GateApp S n)) =
      embedOp c.unitary w := by
  induction c with
  | nil => simp [t9s1_unitary_nil, embedOp_one]
  | cons g cs ih =>
      rw [List.map_cons, t9s1_unitary_cons, ih]
      change embedOp (Circuit.unitary cs) w * embedOp g.gate.mat (g.wires.trans w) = _
      rw [← t9s1_embedOp_trans, ← t9s1_embedOp_mul, t9s1_unitary_cons]

private theorem t9s1_t9_liftAncCircuit_unitary {S : Set Gate} (n : ℕ) {a : ℕ}
    (c : Circuit S a) :
    (t9_liftAncCircuit n c).unitary =
      embedOp c.unitary ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩ :=
  t9s1_liftCircuit_unitary ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩ c

private theorem t9s1_foldr_gate_krausList {S : Set Gate} {n : ℕ}
    (cs : Circuit S n) (k : AdaptiveCircuit S n) :
    (cs.foldr AdaptiveCircuit.gate k).krausList =
      k.krausList.map (fun K => K * cs.unitary) := by
  induction cs with
  | nil =>
      rw [List.foldr_nil, t9s1_unitary_nil]
      simp
  | cons g gs ih =>
      simp only [List.foldr_cons, AdaptiveCircuit.krausList, ih, List.map_map]
      refine List.map_congr_left (fun K _ => ?_)
      dsimp only [Function.comp_apply]
      rw [t9s1_unitary_cons, Matrix.mul_assoc]

/-! ### Part 3: Channel & Partial Trace Helpers -/

private theorem t9s1_isHermitian_conj {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (M : Matrix ι ι ℂ) :
    (M * X * Mᴴ).IsHermitian := by
  change (M * X * Mᴴ)ᴴ = M * X * Mᴴ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hX.eq, Matrix.mul_assoc]

private theorem t9s1_isHermitian_list_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (hl : ∀ A ∈ l, A.IsHermitian) :
    l.sum.IsHermitian := by
  induction l with
  | nil =>
      change (0 : Matrix ι ι ℂ)ᴴ = 0
      exact Matrix.conjTranspose_zero
  | cons a as ih =>
      simp only [List.sum_cons]
      exact (hl a List.mem_cons_self).add (ih fun x hx => hl x (List.mem_cons_of_mem a hx))

private theorem t9s1_channelRef_isHermitian {S : Set Gate} {N m_ref : ℕ}
    (B : AdaptiveCircuit S N)
    {X : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ} (hX : X.IsHermitian) :
    (B.channelRef m_ref X).IsHermitian := by
  dsimp only [AdaptiveCircuit.channelRef]
  refine t9s1_isHermitian_list_sum _ ?_
  intro A hA
  rw [List.mem_map] at hA
  rcases hA with ⟨K, _, rfl⟩
  exact t9s1_isHermitian_conj hX _

private theorem t9s1_proj_conjTranspose {n : ℕ} (q : Fin n) (b : Bool) :
    (AdaptiveCircuit.proj q b)ᴴ = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

private theorem t9s1_proj_mul_self {n : ℕ} (q : Fin n) (b : Bool) :
    AdaptiveCircuit.proj q b * AdaptiveCircuit.proj q b = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem t9s1_proj_add {n : ℕ} (q : Fin n) :
    AdaptiveCircuit.proj q false + AdaptiveCircuit.proj q true = 1 := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; cases y q <;> simp
  · simp [h]

private theorem t9s1_list_sum_map_mul_left_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    (l.map fun K => A * K * B).sum = A * l.sum * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Matrix.mul_add, Matrix.add_mul]

private theorem t9s1_krausList_sum_conj_mul {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n) :
    (B.krausList.map fun K => Kᴴ * K).sum = 1 := by
  induction B with
  | done =>
      simp [AdaptiveCircuit.krausList]
  | gate g k ih =>
      have hU : embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
        t9s1_embedOp_isUnitary (hS g.gate g.mem) g.wires
      rw [Matrix.mem_unitaryGroup_iff'] at hU
      change (embedOp g.gate.mat g.wires)ᴴ * embedOp g.gate.mat g.wires = 1 at hU
      simp only [AdaptiveCircuit.krausList, List.map_map]
      have hcongr : (k.krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * embedOp g.gate.mat g.wires)) =
          ((k.krausList.map fun x => xᴴ * x).map fun K =>
            (embedOp g.gate.mat g.wires)ᴴ * K * embedOp g.gate.mat g.wires) := by
        rw [List.map_map]
        refine List.map_congr_left (fun x _ => ?_)
        simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hcongr, t9s1_list_sum_map_mul_left_right, ih, Matrix.mul_one, hU]
  | measure q k ih =>
      simp only [AdaptiveCircuit.krausList, List.map_append, List.sum_append, List.map_map]
      have hbranch : ∀ b : Bool,
          ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)).sum =
            AdaptiveCircuit.proj q b := by
        intro b
        have hcongr : ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)) =
            (((k b).krausList.map fun x => xᴴ * x).map fun K =>
              (AdaptiveCircuit.proj q b)ᴴ * K * AdaptiveCircuit.proj q b) := by
          rw [List.map_map]
          refine List.map_congr_left (fun x _ => ?_)
          simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [hcongr, t9s1_list_sum_map_mul_left_right, ih b, Matrix.mul_one,
          t9s1_proj_conjTranspose, t9s1_proj_mul_self]
      rw [hbranch false, hbranch true, t9s1_proj_add]

private theorem t9s1_list_sum_kronecker_one_left {m n : ℕ}
    (l : List (Matrix (Qubits n) (Qubits n) ℂ)) :
    (l.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).sum =
      (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Matrix.kronecker_add]

private theorem t9s1_channelRef_kraus_sum_one {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n) (m : ℕ) :
    ((B.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).map
      fun K => Kᴴ * K).sum = 1 := by
  have h1 : ((B.krausList.map fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K).map
      fun K => Kᴴ * K) =
      ((B.krausList.map fun K => Kᴴ * K).map
        fun K => (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left (fun K _ => ?_)
    simp only [Function.comp_apply]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
  rw [h1, t9s1_list_sum_kronecker_one_left, t9s1_krausList_sum_conj_mul hS B, Matrix.one_kronecker_one]

private theorem t9s1_channelRef_sub {S : Set Gate} {n : ℕ} (B : AdaptiveCircuit S n) (m : ℕ)
    (A C : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    B.channelRef m A - B.channelRef m C = B.channelRef m (A - C) := by
  dsimp only [AdaptiveCircuit.channelRef]
  induction B.krausList with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons]
      have ih' : (ks.map fun K => ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * A *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum -
          (ks.map fun K => ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * C *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum =
          (ks.map fun K => ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * (A - C) *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum := ih
      rw [Matrix.mul_sub, Matrix.sub_mul, ← ih']
      abel

private def t9s1_appendEquiv (n a : ℕ) : Qubits n × Qubits a ≃ Qubits (n + a) where
  toFun p := Fin.append p.1 p.2
  invFun z := (fun i => z (Fin.castAdd a i), fun j => z (Fin.natAdd n j))
  left_inv p := by
    ext i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  right_inv z := by
    funext k
    induction k using Fin.addCases with
    | left i => simp [Fin.append_left]
    | right j => simp [Fin.append_right]

private theorem t9s1_kron_one_mul_conj_entry {m_ref n₁ n₂ : ℕ}
    (M : Matrix (Qubits n₁) (Qubits n₂) ℂ)
    (T : Matrix (Fin m_ref × Qubits n₂) (Fin m_ref × Qubits n₂) ℂ)
    (i₁ i₂ : Fin m_ref) (y₁ y₂ : Qubits n₁) :
    (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ M) * T *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ M)ᴴ) (i₁, y₁) (i₂, y₂) =
      ∑ z : Qubits n₂, ∑ w : Qubits n₂,
        M y₁ z * T (i₁, z) (i₂, w) * star (M y₂ w) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kronecker_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  have h1 : ∀ w : Qubits n₂,
      (∑ r : Fin m_ref, ∑ z : Qubits n₂,
          (if i₁ = r then (1 : ℂ) else 0) * M y₁ z * T (r, z) (i₂, w)) =
        ∑ z : Qubits n₂, M y₁ z * T (i₁, z) (i₂, w) := by
    intro w
    rw [Finset.sum_eq_single i₁]
    · simp
    · intro r _ hr; simp [hr.symm]
    · intro hi; exact absurd (Finset.mem_univ i₁) hi
  have h2 : (∑ s : Fin m_ref, ∑ w : Qubits n₂,
      (∑ r : Fin m_ref, ∑ z : Qubits n₂,
        (if i₁ = r then (1 : ℂ) else 0) * M y₁ z * T (r, z) (s, w)) *
      star ((if i₂ = s then (1 : ℂ) else 0) * M y₂ w)) =
      ∑ w : Qubits n₂, (∑ z : Qubits n₂, M y₁ z * T (i₁, z) (i₂, w)) * star (M y₂ w) := by
    rw [Finset.sum_eq_single i₂]
    · refine Finset.sum_congr rfl fun w _ => ?_
      simp only [↓reduceIte, one_mul]
      congr 1
      rw [Finset.sum_eq_single i₁]
      · simp
      · intro r _ hr; simp [hr.symm]
      · intro hi; exact absurd (Finset.mem_univ i₁) hi
    · intro s _ hs; simp [hs.symm]
    · intro hi; exact absurd (Finset.mem_univ i₂) hi
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]

private theorem t9s1_partialTraceAnc_zero {n a m_ref : ℕ} :
    t9_partialTraceAnc (0 : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) =
      0 := by
  ext p₁ p₂
  simp [t9_partialTraceAnc]

private theorem t9s1_partialTraceAnc_add {n a m_ref : ℕ}
    (X Y : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (X + Y) = t9_partialTraceAnc X + t9_partialTraceAnc Y := by
  ext p₁ p₂
  simp [t9_partialTraceAnc, Finset.sum_add_distrib]

private theorem t9s1_partialTraceAnc_sub {n a m_ref : ℕ}
    (X Y : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (X - Y) = t9_partialTraceAnc X - t9_partialTraceAnc Y := by
  ext p₁ p₂
  simp [t9_partialTraceAnc, Finset.sum_sub_distrib]

private theorem t9s1_partialTraceAnc_list_sum {n a m_ref : ℕ}
    (l : List (Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ)) :
    t9_partialTraceAnc l.sum = (l.map t9_partialTraceAnc).sum := by
  induction l with
  | nil => exact t9s1_partialTraceAnc_zero
  | cons X xs ih =>
      simp only [List.sum_cons, List.map_cons, t9s1_partialTraceAnc_add, ih]

private theorem t9s1_isHermitian_partialTraceAnc {n a m_ref : ℕ}
    {X : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ}
    (hX : X.IsHermitian) :
    (t9_partialTraceAnc X).IsHermitian := by
  ext p₁ p₂
  simp only [Matrix.conjTranspose_apply, t9_partialTraceAnc, Matrix.of_apply, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : star (X (p₂.1, Fin.append p₂.2 j) (p₁.1, Fin.append p₁.2 j)) =
      Xᴴ (p₁.1, Fin.append p₁.2 j) (p₂.1, Fin.append p₂.2 j) := rfl
  rw [hij, hX.eq]

private theorem t9s1_partialTraceAnc_kron_term {n a m_ref : ℕ}
    (K : Matrix (Qubits (n + a)) (Qubits (n + a)) ℂ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    t9_partialTraceAnc
        (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K) *
          t9_tensorAncVec (t9_ket0Anc a) ρ *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)ᴴ) =
      ∑ j : Qubits a,
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ AdaptiveCircuit.ancillaCompress K j) * ρ *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ AdaptiveCircuit.ancillaCompress K j)ᴴ := by
  ext ⟨i₁, x₁⟩ ⟨i₂, x₂⟩
  simp only [t9_partialTraceAnc, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [t9s1_kron_one_mul_conj_entry K (t9_tensorAncVec (t9_ket0Anc a) ρ)
        i₁ i₂ (Fin.append x₁ j) (Fin.append x₂ j),
      t9s1_kron_one_mul_conj_entry (AdaptiveCircuit.ancillaCompress K j) ρ i₁ i₂ x₁ x₂]
  rw [← Fintype.sum_equiv (t9s1_appendEquiv n a) (fun p =>
    ∑ w : Qubits (n + a),
      K (Fin.append x₁ j) (Fin.append p.1 p.2) *
        t9_tensorAncVec (t9_ket0Anc a) ρ (i₁, Fin.append p.1 p.2) (i₂, w) *
        star (K (Fin.append x₂ j) w)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  have hket : ∀ (x : Qubits n) (z : Qubits a),
      (t9_ket0Anc a) (fun k => Fin.append x z (Fin.natAdd n k)) =
        if z = (fun _ => false) then 1 else 0 := by
    intro x z
    simp [t9_ket0Anc, Fin.append_right]
  have hinner : ∀ x : Qubits n,
      (∑ z : Qubits a, ∑ w : Qubits (n + a),
        K (Fin.append x₁ j) (Fin.append x z) *
          t9_tensorAncVec (t9_ket0Anc a) ρ (i₁, Fin.append x z) (i₂, w) *
          star (K (Fin.append x₂ j) w)) =
        ∑ w : Qubits (n + a),
          K (Fin.append x₁ j) (Fin.append x (fun _ => false)) *
            t9_tensorAncVec (t9_ket0Anc a) ρ
              (i₁, Fin.append x (fun _ => false)) (i₂, w) *
            star (K (Fin.append x₂ j) w) := by
    intro x
    rw [Finset.sum_eq_single (fun _ => false)]
    · intro z _ hz
      refine Finset.sum_eq_zero fun w _ => ?_
      simp only [t9_tensorAncVec, Matrix.of_apply, hket x z, if_neg hz, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hinner]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fintype.sum_equiv (t9s1_appendEquiv n a) (fun p =>
    K (Fin.append x₁ j) (Fin.append x (fun _ => false)) *
      t9_tensorAncVec (t9_ket0Anc a) ρ
        (i₁, Fin.append x (fun _ => false)) (i₂, Fin.append p.1 p.2) *
      star (K (Fin.append x₂ j) (Fin.append p.1 p.2))) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [t9_tensorAncVec, t9_ket0Anc, AdaptiveCircuit.ancillaCompress,
      Fin.append_left, Fin.append_right]
  · intro w _ hw
    simp [t9_tensorAncVec, t9_ket0Anc, Fin.append_right, hw]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem t9s1_dataChannelRef_eq {S : Set Gate} {n a : ℕ}
    (B : AdaptiveCircuit S (n + a)) (m_ref : ℕ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    B.dataChannelRef m_ref ρ =
      t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec (t9_ket0Anc a) ρ)) := by
  dsimp only [AdaptiveCircuit.dataChannelRef, AdaptiveCircuit.channelRef]
  rw [t9s1_partialTraceAnc_list_sum, List.map_map]
  induction B.krausList with
  | nil => simp
  | cons K ks ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ← ih]
      congr 1
      exact (t9s1_partialTraceAnc_kron_term K ρ).symm

private theorem t9s1_kron_embedAnc_tensorAncVec {n a m_ref : ℕ}
    (U : Matrix (Qubits a) (Qubits a) ℂ) (χ : Qubits a → ℂ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
        embedOp U ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩) *
      t9_tensorAncVec χ ρ *
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
        embedOp U ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩)ᴴ =
      t9_tensorAncVec (U.mulVec χ) ρ := by
  let emb : Fin a ↪ Fin (n + a) := ⟨Fin.natAdd n, Fin.natAdd_injective a n⟩
  have hemb_range : ∀ k : Fin (n + a),
      k ∉ Set.range emb ↔ ∃ i : Fin n, Fin.castAdd a i = k := by
    intro k
    constructor
    · intro hk
      induction k using Fin.addCases with
      | left i => exact ⟨i, rfl⟩
      | right j => exact absurd ⟨j, rfl⟩ hk
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have hlt : (i : ℕ) < n := i.isLt
      have heq : n + (j : ℕ) = (i : ℕ) := by
        simpa [emb, Fin.val_natAdd, Fin.val_castAdd] using congrArg Fin.val hj
      omega
  have hemb_append : ∀ (y : Qubits (n + a)) (x : Qubits n) (u : Qubits a),
      embedOp U emb y (Fin.append x u) =
        if (fun i => y (Fin.castAdd a i)) = x then U (fun j => y (Fin.natAdd n j)) u else 0 := by
    intro y x u
    simp only [embedOp, Matrix.of_apply]
    have hiff : (∀ k : Fin (n + a), k ∉ Set.range emb → y k = Fin.append x u k) ↔
        (fun i => y (Fin.castAdd a i)) = x := by
      constructor
      · intro h
        funext i
        rw [h (Fin.castAdd a i) ((hemb_range (Fin.castAdd a i)).mpr ⟨i, rfl⟩), Fin.append_left]
      · intro h k hk
        rcases (hemb_range k).mp hk with ⟨i, rfl⟩
        rw [Fin.append_left, ← h]
    by_cases h : (fun i => y (Fin.castAdd a i)) = x
    · rw [if_pos (hiff.mpr h), if_pos h]
      congr 1
      funext j
      simp [Fin.append_right, emb]
    · rw [if_neg (mt hiff.mp h), if_neg h]
  ext ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
  rw [t9s1_kron_one_mul_conj_entry (embedOp U emb) (t9_tensorAncVec χ ρ) i₁ i₂ y₁ y₂]
  rw [← Fintype.sum_equiv (t9s1_appendEquiv n a) (fun p =>
    ∑ w : Qubits (n + a),
      embedOp U emb y₁ (Fin.append p.1 p.2) *
        t9_tensorAncVec χ ρ (i₁, Fin.append p.1 p.2) (i₂, w) *
        star (embedOp U emb y₂ w)) _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  have h1 : (∑ x : Qubits n, ∑ u : Qubits a, ∑ w : Qubits (n + a),
      embedOp U emb y₁ (Fin.append x u) *
        t9_tensorAncVec χ ρ (i₁, Fin.append x u) (i₂, w) *
        star (embedOp U emb y₂ w)) =
      ∑ u : Qubits a, ∑ w : Qubits (n + a),
        U (fun j => y₁ (Fin.natAdd n j)) u *
          t9_tensorAncVec χ ρ (i₁, Fin.append (fun i => y₁ (Fin.castAdd a i)) u) (i₂, w) *
          star (embedOp U emb y₂ w) := by
    rw [Finset.sum_eq_single (fun i => y₁ (Fin.castAdd a i))]
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hemb_append y₁ (fun i => y₁ (Fin.castAdd a i)) u, if_pos rfl]
    · intro x _ hx
      refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun w _ => ?_
      rw [hemb_append y₁ x u, if_neg hx.symm, zero_mul, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have h2 : ∀ u : Qubits a,
      (∑ w : Qubits (n + a),
        U (fun j => y₁ (Fin.natAdd n j)) u *
          t9_tensorAncVec χ ρ (i₁, Fin.append (fun i => y₁ (Fin.castAdd a i)) u) (i₂, w) *
          star (embedOp U emb y₂ w)) =
        ∑ v : Qubits a,
          U (fun j => y₁ (Fin.natAdd n j)) u *
            (ρ (i₁, fun i => y₁ (Fin.castAdd a i)) (i₂, fun i => y₂ (Fin.castAdd a i)) *
              χ u * star (χ v)) *
            star (U (fun j => y₂ (Fin.natAdd n j)) v) := by
    intro u
    rw [← Fintype.sum_equiv (t9s1_appendEquiv n a) (fun p =>
      U (fun j => y₁ (Fin.natAdd n j)) u *
        t9_tensorAncVec χ ρ (i₁, Fin.append (fun i => y₁ (Fin.castAdd a i)) u)
          (i₂, Fin.append p.1 p.2) *
        star (embedOp U emb y₂ (Fin.append p.1 p.2))) _ (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (fun i => y₂ (Fin.castAdd a i))]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hemb_append y₂ (fun i => y₂ (Fin.castAdd a i)) v, if_pos rfl]
      simp [t9_tensorAncVec, Fin.append_left, Fin.append_right]
    · intro x _ hx
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [hemb_append y₂ x v, if_neg hx.symm, star_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [h2]
  simp only [t9_tensorAncVec, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc ∑ u : Qubits a, ∑ v : Qubits a,
        U (fun j => y₁ (Fin.natAdd n j)) u *
          (ρ (i₁, fun i => y₁ (Fin.castAdd a i)) (i₂, fun i => y₂ (Fin.castAdd a i)) *
            χ u * star (χ v)) *
          star (U (fun j => y₂ (Fin.natAdd n j)) v)
      = ∑ u : Qubits a,
          (ρ (i₁, fun i => y₁ (Fin.castAdd a i)) (i₂, fun i => y₂ (Fin.castAdd a i)) *
            (U (fun j => y₁ (Fin.natAdd n j)) u * χ u)) *
          ∑ v : Qubits a, star (U (fun j => y₂ (Fin.natAdd n j)) v * χ v) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [star_mul]
          ring
    _ = ρ (i₁, fun i => y₁ (Fin.castAdd a i)) (i₂, fun i => y₂ (Fin.castAdd a i)) *
          (∑ u : Qubits a, U (fun j => y₁ (Fin.natAdd n j)) u * χ u) *
          star (∑ v : Qubits a, U (fun j => y₂ (Fin.natAdd n j)) v * χ v) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, star_sum]

private theorem t9s1_prependAnc_dataChannelRef {S : Set Gate} {n a : ℕ}
    (cAnc : Circuit S a) (B : AdaptiveCircuit S (n + a)) (m_ref : ℕ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    (t9_prependCircuit (t9_liftAncCircuit n cAnc) B).dataChannelRef m_ref ρ =
      t9_partialTraceAnc
        (B.channelRef m_ref (t9_tensorAncVec (cAnc.unitary.mulVec (t9_ket0Anc a)) ρ)) := by
  rw [t9s1_dataChannelRef_eq]
  refine congrArg t9_partialTraceAnc ?_
  dsimp only [t9_prependCircuit, AdaptiveCircuit.channelRef]
  rw [t9s1_foldr_gate_krausList, List.map_map]
  have hmap : (B.krausList.map ((fun K => ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K) *
        t9_tensorAncVec (t9_ket0Anc a) ρ *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)ᴴ) ∘
        fun K => K * (t9_liftAncCircuit n cAnc).unitary)) =
      (B.krausList.map fun K =>
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K) *
          (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (t9_liftAncCircuit n cAnc).unitary) *
            t9_tensorAncVec (t9_ket0Anc a) ρ *
            ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (t9_liftAncCircuit n cAnc).unitary)ᴴ) *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)ᴴ) := by
    refine List.map_congr_left fun K _ => ?_
    simp only [Function.comp_apply]
    have h1 : (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (K * (t9_liftAncCircuit n cAnc).unitary) =
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K) *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (t9_liftAncCircuit n cAnc).unitary) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [h1, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [hmap, t9s1_t9_liftAncCircuit_unitary, t9s1_kron_embedAnc_tensorAncVec]

private def t9s1_traceKraus {n a m_ref : ℕ} (j : Qubits a) :
    Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits (n + a)) ℂ :=
  (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
    Matrix.of fun (x : Qubits n) (y : Qubits (n + a)) =>
      if y = Fin.append x j then 1 else 0

private noncomputable def t9s1_traceKrausList (n a m_ref : ℕ) :
    List (Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits (n + a)) ℂ) :=
  (Finset.univ : Finset (Qubits a)).toList.map (t9s1_traceKraus (n := n) (m_ref := m_ref))

private theorem t9s1_partialTraceAnc_eq_kraus {n a m_ref : ℕ}
    (X : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc X =
      ((t9s1_traceKrausList n a m_ref).map fun K => K * X * Kᴴ).sum := by
  ext ⟨i₁, x₁⟩ ⟨i₂, x₂⟩
  simp only [t9_partialTraceAnc, Matrix.of_apply, t9s1_traceKrausList, List.map_map]
  have hsum_list : ∀ (l : List (Qubits a)),
      ((l.map (fun j => t9s1_traceKraus (n := n) (m_ref := m_ref) j * X *
        (t9s1_traceKraus (n := n) (m_ref := m_ref) j)ᴴ)).sum) (i₁, x₁) (i₂, x₂) =
        (l.map fun j => X (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons j js ih =>
        simp only [List.map_cons, List.sum_cons, Matrix.add_apply, ih]
        congr 1
        dsimp only [t9s1_traceKraus]
        rw [t9s1_kron_one_mul_conj_entry _ X i₁ i₂ x₁ x₂]
        rw [Finset.sum_eq_single (Fin.append x₁ j)]
        · simp only [Matrix.of_apply, ↓reduceIte, one_mul]
          rw [Finset.sum_eq_single (Fin.append x₂ j)]
          · simp
          · intro w _ hw; simp [hw]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro z _ hz
          refine Finset.sum_eq_zero fun w _ => ?_
          simp [hz]
        · intro h; exact absurd (Finset.mem_univ _) h
  have hcomp : ((Finset.univ : Finset (Qubits a)).toList.map
        ((fun K => K * X * Kᴴ) ∘ t9s1_traceKraus (n := n) (m_ref := m_ref))) =
      ((Finset.univ : Finset (Qubits a)).toList.map fun j =>
        t9s1_traceKraus (n := n) (m_ref := m_ref) j * X *
          (t9s1_traceKraus (n := n) (m_ref := m_ref) j)ᴴ) := rfl
  rw [hcomp, hsum_list]
  symm
  exact Finset.sum_map_toList _ _

private theorem t9s1_traceKrausList_sum_conj_mul (n a m_ref : ℕ) :
    ((t9s1_traceKrausList n a m_ref).map fun K => Kᴴ * K).sum = 1 := by
  dsimp only [t9s1_traceKrausList]
  rw [List.map_map]
  have hterm : ∀ j : Qubits a,
      (t9s1_traceKraus (n := n) (m_ref := m_ref) j)ᴴ * t9s1_traceKraus (n := n) (m_ref := m_ref) j =
        (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
          Matrix.diagonal (fun y : Qubits (n + a) =>
            if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0) := by
    intro j
    dsimp only [t9s1_traceKraus]
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, one_mul]
    congr 1
    ext y₁ y₂
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.diagonal_apply]
    by_cases hy : y₁ = y₂
    · subst hy
      rw [if_pos rfl]
      by_cases hj : (fun k => y₁ (Fin.natAdd n k)) = j
      · rw [if_pos hj]
        rw [Finset.sum_eq_single (fun i => y₁ (Fin.castAdd a i))]
        · have hyeq : y₁ = Fin.append (fun i => y₁ (Fin.castAdd a i)) j := by
            rw [← hj]
            exact ((t9s1_appendEquiv n a).right_inv y₁).symm
          rw [if_pos hyeq, mul_one]
          simp
        · intro x _ hx
          have hne : y₁ ≠ Fin.append x j := by
            intro heq
            apply hx
            funext i
            rw [heq, Fin.append_left]
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hj]
        refine Finset.sum_eq_zero fun x _ => ?_
        have hne : y₁ ≠ Fin.append x j := by
          intro heq
          apply hj
          funext k
          rw [heq, Fin.append_right]
        simp [hne]
    · rw [if_neg hy]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h1 : y₁ = Fin.append x j
      · have h2 : y₂ ≠ Fin.append x j := fun h => hy (h1.trans h.symm)
        simp [h1, h2]
      · simp [h1]
  have hcomp : ((Finset.univ : Finset (Qubits a)).toList.map
        ((fun K => Kᴴ * K) ∘ t9s1_traceKraus (n := n) (m_ref := m_ref))) =
      ((Finset.univ : Finset (Qubits a)).toList.map fun j =>
        (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
          Matrix.diagonal (fun y : Qubits (n + a) =>
            if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0)) := by
    refine List.map_congr_left fun j _ => ?_
    exact hterm j
  rw [hcomp]
  have hsum : ∀ (l : List (Qubits a)),
      (l.map fun j => (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
        Matrix.diagonal (fun y : Qubits (n + a) =>
          if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0)).sum =
      (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
        Matrix.diagonal (fun y : Qubits (n + a) =>
          (l.map fun j => if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0).sum) := by
    intro l
    induction l with
    | nil => simp
    | cons j js ih =>
        simp only [List.map_cons, List.sum_cons, ih, ← Matrix.kronecker_add, ← Matrix.diagonal_add]
  rw [hsum]
  have hdiag : (fun y : Qubits (n + a) =>
      ((Finset.univ : Finset (Qubits a)).toList.map fun j =>
        if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0).sum) =
      fun _ => (1 : ℂ) := by
    funext y
    have hsum_eq : ((Finset.univ : Finset (Qubits a)).toList.map fun j =>
        if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0).sum =
        ∑ j : Qubits a, if (fun k => y (Fin.natAdd n k)) = j then (1 : ℂ) else 0 := by
      rw [← Finset.sum_map_toList]
    rw [hsum_eq, Finset.sum_ite_eq Finset.univ (fun k => y (Fin.natAdd n k))]
    simp
  rw [hdiag, Matrix.diagonal_one, Matrix.one_kronecker_one]

private theorem t9s1_partialTraceAnc_traceNorm_le {n a m_ref : ℕ}
    {X : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ}
    (hX : X.IsHermitian) :
    WildeQIT.traceNorm (t9_partialTraceAnc X) ≤ WildeQIT.traceNorm X := by
  rw [t9s1_partialTraceAnc_eq_kraus]
  exact t9s1_cptp_traceNorm_le_rect (t9s1_traceKrausList n a m_ref)
    (t9s1_traceKrausList_sum_conj_mul n a m_ref) hX

private theorem t9s1_isDensityOperator_partialTraceAnc {n a m_ref : ℕ}
    {σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ}
    (hσ : WildeQIT.IsDensityOperator σ) :
    WildeQIT.IsDensityOperator (t9_partialTraceAnc σ) := by
  rw [t9s1_partialTraceAnc_eq_kraus]
  refine ⟨t9s1_posSemidef_list_sum fun M hM => ?_, ?_⟩
  · rcases List.mem_map.mp hM with ⟨K, _, rfl⟩
    exact hσ.1.mul_mul_conjTranspose_same K
  · rw [t9s1_trace_list_map_kraus, t9s1_traceKrausList_sum_conj_mul, one_mul, hσ.2]

private def t9s1_liftAncMat {n a : ℕ} (χ : Qubits a → ℂ) :
    Matrix (Qubits (n + a)) (Qubits n) ℂ :=
  Matrix.of fun y x =>
    if (fun i => y (Fin.castAdd a i)) = x then χ (fun j => y (Fin.natAdd n j)) else 0

private theorem t9s1_tensorAncVec_eq_conj {n a m_ref : ℕ} (χ : Qubits a → ℂ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    t9_tensorAncVec χ ρ =
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ) * ρ *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ)ᴴ := by
  ext ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
  rw [t9s1_kron_one_mul_conj_entry (t9s1_liftAncMat (n := n) χ) ρ i₁ i₂ y₁ y₂]
  rw [Finset.sum_eq_single (fun i => y₁ (Fin.castAdd a i))]
  · rw [Finset.sum_eq_single (fun i => y₂ (Fin.castAdd a i))]
    · simp only [t9s1_liftAncMat, Matrix.of_apply, ↓reduceIte, t9_tensorAncVec]
      ring
    · intro x₂ _ hx₂
      simp [t9s1_liftAncMat, hx₂.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro x₁ _ hx₁
    refine Finset.sum_eq_zero fun x₂ _ => ?_
    simp [t9s1_liftAncMat, hx₁.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem t9s1_liftAncMat_sub {n a : ℕ} (χ₁ χ₂ : Qubits a → ℂ) :
    t9s1_liftAncMat (n := n) χ₁ - t9s1_liftAncMat (n := n) χ₂ =
      t9s1_liftAncMat (n := n) (fun z => χ₁ z - χ₂ z) := by
  ext y x
  simp only [Matrix.sub_apply, t9s1_liftAncMat, Matrix.of_apply]
  split_ifs <;> simp

private theorem t9s1_liftAncMat_conjTranspose_mul {n a : ℕ} (χ : Qubits a → ℂ) :
    (t9s1_liftAncMat (n := n) χ)ᴴ * t9s1_liftAncMat (n := n) χ =
      ((∑ z : Qubits a, ‖χ z‖ ^ 2 : ℝ) : ℂ) • (1 : Matrix (Qubits n) (Qubits n) ℂ) := by
  ext x₁ x₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, t9s1_liftAncMat, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [← Fintype.sum_equiv (t9s1_appendEquiv n a) (fun p =>
    star (if p.1 = x₁ then χ p.2 else 0) * (if p.1 = x₂ then χ p.2 else 0)) _ (fun p => by
      simp [t9s1_appendEquiv, Fin.append_left, Fin.append_right])]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x₁]
  · by_cases hx : x₁ = x₂
    · subst hx
      simp only [↓reduceIte, mul_one]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    · simp [hx]
  · intro x _ hx; simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem t9s1_kron_liftAncMat_conjTranspose_mul {n a m_ref : ℕ} (χ : Qubits a → ℂ) :
    ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ)ᴴ *
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ) =
      ((∑ z : Qubits a, ‖χ z‖ ^ 2 : ℝ) : ℂ) •
        (1 : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    one_mul, t9s1_liftAncMat_conjTranspose_mul]
  ext ⟨i₁, x₁⟩ ⟨i₂, x₂⟩
  by_cases hi : i₁ = i₂ <;> by_cases hx : x₁ = x₂ <;> simp [hi, hx]

private theorem t9s1_isDensityOperator_tensorAncVec {n a m_ref : ℕ}
    {χ : Qubits a → ℂ} (hχ : (∑ z : Qubits a, ‖χ z‖ ^ 2) = 1)
    {ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ}
    (hρ : WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (t9_tensorAncVec χ ρ) := by
  rw [t9s1_tensorAncVec_eq_conj]
  refine ⟨hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_mul_cycle, t9s1_kron_liftAncMat_conjTranspose_mul, hχ,
    Complex.ofReal_one, one_smul, one_mul, hρ.2]

private theorem t9s1_tensorAncVec_phase {n a m_ref : ℕ} (Φ : ℝ) (χ : Qubits a → ℂ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    t9_tensorAncVec (fun z => Complex.exp ((Φ : ℂ) * Complex.I) * χ z) ρ =
      t9_tensorAncVec χ ρ := by
  ext p₁ p₂
  simp only [t9_tensorAncVec, Matrix.of_apply]
  have hunit : Complex.exp ((Φ : ℂ) * Complex.I) *
      star (Complex.exp ((Φ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
    simp
  rw [star_mul]
  calc ρ (p₁.1, fun i => p₁.2 (Fin.castAdd a i)) (p₂.1, fun i => p₂.2 (Fin.castAdd a i)) *
        (Complex.exp ((Φ : ℂ) * Complex.I) * χ (fun j => p₁.2 (Fin.natAdd n j))) *
        (star (χ (fun j => p₂.2 (Fin.natAdd n j))) * star (Complex.exp ((Φ : ℂ) * Complex.I)))
      = ρ (p₁.1, fun i => p₁.2 (Fin.castAdd a i)) (p₂.1, fun i => p₂.2 (Fin.castAdd a i)) *
          χ (fun j => p₁.2 (Fin.natAdd n j)) * star (χ (fun j => p₂.2 (Fin.natAdd n j))) *
          (Complex.exp ((Φ : ℂ) * Complex.I) * star (Complex.exp ((Φ : ℂ) * Complex.I))) := by ring
    _ = _ := by rw [hunit, mul_one]

private theorem t9s1_channelWithAnc_approx_le {S : Set Gate}
    (hS : ∀ g ∈ S, g.IsUnitary) {n a : ℕ}
    (B : AdaptiveCircuit S (n + a))
    {χ₁ χ₂ : Qubits a → ℂ}
    (hχ₁ : (∑ z : Qubits a, ‖χ₁ z‖ ^ 2) = 1)
    (hχ₂ : (∑ z : Qubits a, ‖χ₂ z‖ ^ 2) = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (Φ : ℝ)
    (hdist : Real.sqrt (∑ z : Qubits a,
      ‖Complex.exp ((Φ : ℂ) * Complex.I) * χ₁ z - χ₂ z‖ ^ 2) ≤ δ)
    (m_ref : ℕ)
    {ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ}
    (hρ : WildeQIT.IsDensityOperator ρ) :
    WildeQIT.traceDist
      (t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec χ₁ ρ)))
      (t9_partialTraceAnc (B.channelRef m_ref (t9_tensorAncVec χ₂ ρ))) ≤ 2 * δ := by
  let χ₁' : Qubits a → ℂ := fun z => Complex.exp ((Φ : ℂ) * Complex.I) * χ₁ z
  have hχ₁' : (∑ z : Qubits a, ‖χ₁' z‖ ^ 2) = 1 := by
    calc ∑ z : Qubits a, ‖χ₁' z‖ ^ 2
        = ∑ z : Qubits a, ‖χ₁ z‖ ^ 2 := by
            refine Finset.sum_congr rfl fun z _ => ?_
            simp [χ₁', Complex.norm_exp_ofReal_mul_I]
      _ = 1 := hχ₁
  have hten₁ : t9_tensorAncVec χ₁' ρ = t9_tensorAncVec χ₁ ρ :=
    t9s1_tensorAncVec_phase Φ χ₁ ρ
  rw [← hten₁]
  let M₁ := (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ₁'
  let M₂ := (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) χ₂
  let Δ := t9_tensorAncVec χ₁' ρ - t9_tensorAncVec χ₂ ρ
  have hΔ_eq : Δ = M₁ * ρ * M₁ᴴ - M₂ * ρ * M₂ᴴ := by
    dsimp [Δ, M₁, M₂]
    rw [t9s1_tensorAncVec_eq_conj (n := n) χ₁' ρ, t9s1_tensorAncVec_eq_conj (n := n) χ₂ ρ]
  have hΔ_herm : Δ.IsHermitian :=
    (hρ.1.mul_mul_conjTranspose_same M₁).isHermitian.sub
      (hρ.1.mul_mul_conjTranspose_same M₂).isHermitian |> fun h => by
        rw [← hΔ_eq] at h; exact h
  have hΔ_bound : WildeQIT.traceNorm Δ ≤ 2 * δ := by
    obtain ⟨S_u, hS_u, hnorm⟩ := t9s1_traceNorm_eq_trace_unitary hΔ_herm
    rw [hnorm]
    let R := CFC.sqrt ρ
    have hR_nonneg : 0 ≤ R := CFC.sqrt_nonneg ρ
    have hR_herm : R.IsHermitian := (Matrix.LE.le.posSemidef hR_nonneg).isHermitian
    have hRR : R * R = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.1.nonneg
    have hRRH : R * Rᴴ = ρ := by rw [hR_herm.eq, hRR]
    let A := (M₁ - M₂) * R
    let B₁ := M₁ * R
    let B₂ := M₂ * R
    have hΔ_fac : Δ = A * B₁ᴴ + B₂ * Aᴴ := by
      rw [hΔ_eq]
      dsimp [A, B₁, B₂]
      conv_lhs => rw [← hRRH]
      simp only [Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.conjTranspose_sub, Matrix.mul_assoc]
      abel
    have hM₁_iso : M₁ᴴ * M₁ = 1 := by
      dsimp [M₁]
      rw [t9s1_kron_liftAncMat_conjTranspose_mul, hχ₁', Complex.ofReal_one, one_smul]
    have hM₂_iso : M₂ᴴ * M₂ = 1 := by
      dsimp [M₂]
      rw [t9s1_kron_liftAncMat_conjTranspose_mul, hχ₂, Complex.ofReal_one, one_smul]
    have hF_R : (Matrix.trace (R * Rᴴ)).re = 1 := by
      rw [hRRH, hρ.2, Complex.one_re]
    have hF_B₁ : (Matrix.trace (B₁ * B₁ᴴ)).re = 1 := by
      have h1 : Matrix.trace (B₁ * B₁ᴴ) = Matrix.trace (B₁ᴴ * B₁) := Matrix.trace_mul_comm _ _
      have h2 : B₁ᴴ * B₁ = Rᴴ * R := by
        dsimp [B₁]
        calc (M₁ * R)ᴴ * (M₁ * R) = Rᴴ * (M₁ᴴ * M₁) * R := by
                simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = Rᴴ * R := by rw [hM₁_iso, Matrix.mul_one]
      rw [h1, h2, Matrix.trace_mul_comm, hF_R]
    have hF_B₂ : (Matrix.trace (B₂ * B₂ᴴ)).re = 1 := by
      have h1 : Matrix.trace (B₂ * B₂ᴴ) = Matrix.trace (B₂ᴴ * B₂) := Matrix.trace_mul_comm _ _
      have h2 : B₂ᴴ * B₂ = Rᴴ * R := by
        dsimp [B₂]
        calc (M₂ * R)ᴴ * (M₂ * R) = Rᴴ * (M₂ᴴ * M₂) * R := by
                simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = Rᴴ * R := by rw [hM₂_iso, Matrix.mul_one]
      rw [h1, h2, Matrix.trace_mul_comm, hF_R]
    have hMdiff : M₁ - M₂ =
        (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ t9s1_liftAncMat (n := n) (fun z => χ₁' z - χ₂ z) := by
      ext ⟨i₁, y₁⟩ ⟨i₂, x₂⟩
      by_cases h : i₁ = i₂
      · subst h
        simp only [M₁, M₂, Matrix.sub_apply, Matrix.kronecker_apply, Matrix.one_apply, ↓reduceIte,
          one_mul, t9s1_liftAncMat, Matrix.of_apply]
        split_ifs <;> simp
      · simp [M₁, M₂, h]
    have hF_A : (Matrix.trace (A * Aᴴ)).re ≤ δ ^ 2 := by
      have h1 : Matrix.trace (A * Aᴴ) = Matrix.trace (Aᴴ * A) := Matrix.trace_mul_comm _ _
      have h2 : Aᴴ * A = ((∑ z : Qubits a, ‖χ₁' z - χ₂ z‖ ^ 2 : ℝ) : ℂ) • (Rᴴ * R) := by
        dsimp [A]
        rw [hMdiff]
        calc (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
                t9s1_liftAncMat (n := n) (fun z => χ₁' z - χ₂ z)) * R)ᴴ *
              (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
                t9s1_liftAncMat (n := n) (fun z => χ₁' z - χ₂ z)) * R)
            = Rᴴ * (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
                t9s1_liftAncMat (n := n) (fun z => χ₁' z - χ₂ z))ᴴ *
              ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ
                t9s1_liftAncMat (n := n) (fun z => χ₁' z - χ₂ z))) * R := by
                simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = Rᴴ * (((∑ z : Qubits a, ‖χ₁' z - χ₂ z‖ ^ 2 : ℝ) : ℂ) • 1) * R := by
                rw [t9s1_kron_liftAncMat_conjTranspose_mul]
          _ = ((∑ z : Qubits a, ‖χ₁' z - χ₂ z‖ ^ 2 : ℝ) : ℂ) • (Rᴴ * R) := by
                simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      rw [h1, h2, Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, hRRH, hρ.2, mul_one,
        Complex.ofReal_re]
      have hsq : Real.sqrt (∑ z : Qubits a, ‖χ₁' z - χ₂ z‖ ^ 2) ^ 2 ≤ δ ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hdist 2
      rwa [Real.sq_sqrt (Finset.sum_nonneg fun z _ => sq_nonneg _)] at hsq
    have hsqrt_A : Real.sqrt (Matrix.trace (A * Aᴴ)).re ≤ δ := by
      calc Real.sqrt (Matrix.trace (A * Aᴴ)).re
          ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hF_A
        _ = δ := Real.sqrt_sq hδ
    have hterm1 : ‖Matrix.trace ((S_u * A) * B₁ᴴ)‖ ≤ δ := by
      calc ‖Matrix.trace ((S_u * A) * B₁ᴴ)‖
          ≤ Real.sqrt (Matrix.trace ((S_u * A) * (S_u * A)ᴴ)).re *
              Real.sqrt (Matrix.trace (B₁ * B₁ᴴ)).re :=
              t9s1_frobenius_cauchy_schwarz (S_u * A) B₁
        _ = Real.sqrt (Matrix.trace (A * Aᴴ)).re * 1 := by
              rw [t9s1_trace_unitary_mul_frobenius hS_u, hF_B₁, Real.sqrt_one]
        _ ≤ δ := by rwa [mul_one]
    have hterm2 : ‖Matrix.trace ((S_u * B₂) * Aᴴ)‖ ≤ δ := by
      calc ‖Matrix.trace ((S_u * B₂) * Aᴴ)‖
          ≤ Real.sqrt (Matrix.trace ((S_u * B₂) * (S_u * B₂)ᴴ)).re *
              Real.sqrt (Matrix.trace (A * Aᴴ)).re :=
              t9s1_frobenius_cauchy_schwarz (S_u * B₂) A
        _ = 1 * Real.sqrt (Matrix.trace (A * Aᴴ)).re := by
              rw [t9s1_trace_unitary_mul_frobenius hS_u, hF_B₂, Real.sqrt_one]
        _ ≤ δ := by rwa [one_mul]
    have htr_SΔ : Matrix.trace (S_u * Δ) =
        Matrix.trace ((S_u * A) * B₁ᴴ) + Matrix.trace ((S_u * B₂) * Aᴴ) := by
      rw [hΔ_fac, Matrix.mul_add, Matrix.trace_add,
        ← Matrix.mul_assoc S_u A B₁ᴴ, ← Matrix.mul_assoc S_u B₂ Aᴴ]
    calc (Matrix.trace (S_u * Δ)).re
        ≤ ‖Matrix.trace (S_u * Δ)‖ := Complex.re_le_norm _
      _ = ‖Matrix.trace ((S_u * A) * B₁ᴴ) + Matrix.trace ((S_u * B₂) * Aᴴ)‖ := by rw [htr_SΔ]
      _ ≤ ‖Matrix.trace ((S_u * A) * B₁ᴴ)‖ + ‖Matrix.trace ((S_u * B₂) * Aᴴ)‖ := norm_add_le _ _
      _ ≤ δ + δ := add_le_add hterm1 hterm2
      _ = 2 * δ := by ring
  unfold WildeQIT.traceDist
  rw [← t9s1_partialTraceAnc_sub, t9s1_channelRef_sub]
  have hcptp : WildeQIT.traceNorm (B.channelRef m_ref Δ) ≤ WildeQIT.traceNorm Δ := by
    dsimp only [AdaptiveCircuit.channelRef]
    have hmap : (B.krausList.map fun K =>
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K) * Δ *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)ᴴ) =
        ((B.krausList.map fun K => (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K).map
          fun K => K * Δ * Kᴴ) := by
      rw [List.map_map]; rfl
    rw [hmap]
    exact t9s1_cptp_traceNorm_le
      (B.krausList.map fun K => (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)
      (t9s1_channelRef_kraus_sum_one hS B m_ref) hΔ_herm
  exact (t9s1_partialTraceAnc_traceNorm_le (t9s1_channelRef_isHermitian B hΔ_herm)).trans
    (hcptp.trans hΔ_bound)

/-! ### Part 4: Parallel Resource-State Preparation (`prep_resource_states`) -/

private def t9s1_singleWire {N : ℕ} (q : Fin N) : Fin 1 ↪ Fin N :=
  ⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩

private def t9s1_lift1 {S : Set Gate} {N : ℕ} (q : Fin N) (c : Circuit S 1) : Circuit S N :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans (t9s1_singleWire q)⟩

private theorem t9s1_lift1_size {S : Set Gate} {N : ℕ} (q : Fin N) (c : Circuit S 1) :
    (t9s1_lift1 q c).size = c.size := by
  simp [t9s1_lift1, Circuit.size]

private theorem t9s1_lift1_unitary {S : Set Gate} {N : ℕ} (q : Fin N) (c : Circuit S 1) :
    (t9s1_lift1 q c).unitary = embedOp c.unitary (t9s1_singleWire q) :=
  t9s1_liftCircuit_unitary (t9s1_singleWire q) c

private def t9s1_prodVec {N : ℕ} (f : Fin N → Bool → ℂ) : Qubits N → ℂ :=
  fun z => ∏ q : Fin N, f q (z q)

private def t9s1_applyOnWire (U : Matrix (Qubits 1) (Qubits 1) ℂ) (g : Bool → ℂ) : Bool → ℂ :=
  fun b => (U.mulVec (fun u => g (u 0))) (fun _ => b)

private theorem t9s1_embedOp_mulVec_prodVec {N : ℕ} (A : Matrix (Qubits 1) (Qubits 1) ℂ)
    (p : Fin N) (f : Fin N → Bool → ℂ) :
    (embedOp A (t9s1_singleWire p)).mulVec (t9s1_prodVec f) =
      t9s1_prodVec (Function.update f p (t9s1_applyOnWire A (f p))) := by
  ext y
  simp only [Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply, t9s1_prodVec]
  let zOf : Bool → Qubits N := Function.update y p
  have hne_z : ∀ z : Qubits N, (¬ ∀ q : Fin N, q ∉ Set.range (t9s1_singleWire p) → y q = z q) →
      ∀ b : Bool, z ≠ zOf b := by
    intro z hnot b heq
    apply hnot
    intro q hq
    have hqp : q ≠ p := fun h => hq ⟨0, h.symm⟩
    rw [heq]
    exact (Function.update_of_ne hqp b y).symm
  have hsplit : (∑ z : Qubits N,
      (if ∀ q : Fin N, q ∉ Set.range (t9s1_singleWire p) → y q = z q then
        A (y ∘ t9s1_singleWire p) (z ∘ t9s1_singleWire p) else 0) *
      ∏ q : Fin N, f q (z q)) =
      ∑ b : Bool, A (fun _ => y p) (fun _ => b) * ∏ q : Fin N, f q (zOf b q) := by
    calc ∑ z : Qubits N,
          (if ∀ q : Fin N, q ∉ Set.range (t9s1_singleWire p) → y q = z q then
            A (y ∘ t9s1_singleWire p) (z ∘ t9s1_singleWire p) else 0) *
          ∏ q : Fin N, f q (z q)
        = ∑ z ∈ ({zOf false, zOf true} : Finset (Qubits N)),
            A (y ∘ t9s1_singleWire p) (z ∘ t9s1_singleWire p) * ∏ q : Fin N, f q (z q) := by
            rw [← Finset.sum_subset (Finset.subset_univ {zOf false, zOf true})]
            · refine Finset.sum_congr rfl fun z hz => ?_
              have hcond : ∀ q : Fin N, q ∉ Set.range (t9s1_singleWire p) → y q = z q := by
                rcases Finset.mem_insert.mp hz with rfl | hz'
                · intro q hq
                  have hqp : q ≠ p := fun h => hq ⟨0, h.symm⟩
                  exact (Function.update_of_ne hqp false y).symm
                · rw [Finset.mem_singleton.mp hz']
                  intro q hq
                  have hqp : q ≠ p := fun h => hq ⟨0, h.symm⟩
                  exact (Function.update_of_ne hqp true y).symm
              rw [if_pos hcond]
            · intro z _ hz
              have hnot : ¬ ∀ q : Fin N, q ∉ Set.range (t9s1_singleWire p) → y q = z q := by
                intro hcond
                apply hz
                have hz_eq : z = zOf (z p) := by
                  funext q
                  dsimp only [zOf]
                  by_cases hqp : q = p
                  · subst hqp; simp
                  · rw [Function.update_of_ne hqp]
                    exact (hcond q fun ⟨_, h⟩ => hqp h.symm).symm
                cases hzp : z p
                · exact Finset.mem_insert_self _ _ |> fun m => by rwa [hz_eq, hzp]
                · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) |> fun m => by
                    rwa [hz_eq, hzp]
              rw [if_neg hnot, zero_mul]
      _ = ∑ b : Bool, A (fun _ => y p) (fun _ => b) * ∏ q : Fin N, f q (zOf b q) := by
            have hne : zOf false ≠ zOf true := by
              intro h
              have := congrFun h p
              simp [zOf] at this
            have hy0 : y ∘ t9s1_singleWire p = fun _ => y p := rfl
            have hz0 : zOf false ∘ t9s1_singleWire p = fun _ => false := by
              funext _; exact Function.update_self p false y
            have hz1 : zOf true ∘ t9s1_singleWire p = fun _ => true := by
              funext _; exact Function.update_self p true y
            rw [Finset.sum_pair hne, Fintype.sum_bool, add_comm, hy0, hz0, hz1]
  rw [hsplit]
  have hprod : ∀ b : Bool,
      (∏ q : Fin N, f q (zOf b q)) =
        f p b * ∏ q ∈ Finset.univ.erase p, f q (y q) := by
    intro b
    rw [← Finset.mul_prod_erase Finset.univ (fun q => f q (zOf b q)) (Finset.mem_univ p)]
    congr 1
    · simp [zOf]
    · refine Finset.prod_congr rfl fun q hq => ?_
      dsimp only [zOf]
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
  simp_rw [hprod]
  have hfactor : (∑ b : Bool, A (fun _ => y p) (fun _ => b) *
        (f p b * ∏ q ∈ Finset.univ.erase p, f q (y q))) =
      (∑ b : Bool, A (fun _ => y p) (fun _ => b) * f p b) *
        ∏ q ∈ Finset.univ.erase p, f q (y q) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => by ring
  rw [hfactor]
  rw [← Finset.mul_prod_erase Finset.univ (fun q => Function.update f p (t9s1_applyOnWire A (f p)) q (y q)) (Finset.mem_univ p)]
  congr 1
  · simp only [Function.update_self, t9s1_applyOnWire, Matrix.mulVec, dotProduct]
    symm
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool)
      (fun u => A (fun _ => y p) u * f p (u 0))
      (fun b => A (fun _ => y p) (fun _ => b) * f p b)
      (fun u => by
        have hu : (fun _ : Fin 1 => Equiv.funUnique (Fin 1) Bool u) = u := by
          funext i; rw [Fin.eq_zero i]; rfl
        rw [hu]; rfl)]
  · refine Finset.prod_congr rfl fun q hq => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]

private def t9s1_prepCirc {L M : ℕ} (c : Fin L → Circuit CliffordT 1) :
    List (Fin L) → Circuit CliffordT (L + M)
  | [] => []
  | i :: is => t9s1_lift1 (Fin.castAdd M i) (c i) ++ t9s1_prepCirc c is

private theorem t9s1_prepCirc_size {L M : ℕ} (c : Fin L → Circuit CliffordT 1)
    (l : List (Fin L)) :
    (t9s1_prepCirc (M := M) c l).size = (l.map fun i => (c i).size).sum := by
  induction l with
  | nil => simp [t9s1_prepCirc, Circuit.size]
  | cons i is ih =>
      simp only [t9s1_prepCirc, Circuit.size, List.length_append, List.map_cons, List.sum_cons]
      have h1 : (t9s1_lift1 (Fin.castAdd M i) (c i)).length = (c i).size := t9s1_lift1_size _ _
      dsimp only [Circuit.size] at ih h1
      omega

private theorem t9s1_prepCirc_mulVec {L M : ℕ} (c : Fin L → Circuit CliffordT 1)
    (l : List (Fin L)) (hl : l.Nodup) (f : Fin (L + M) → Bool → ℂ) :
    (t9s1_prepCirc (M := M) c l).unitary.mulVec (t9s1_prodVec f) =
      t9s1_prodVec (fun q => match finSumFinEquiv.symm q with
        | Sum.inl i => if i ∈ l then t9s1_applyOnWire (c i).unitary (f q) else f q
        | Sum.inr _ => f q) := by
  induction l generalizing f with
  | nil =>
      simp only [t9s1_prepCirc, t9s1_unitary_nil, Matrix.one_mulVec, List.not_mem_nil,
        ↓reduceIte]
      congr 1; funext q
      cases finSumFinEquiv.symm q <;> rfl
  | cons i is ih =>
      rcases List.nodup_cons.mp hl with ⟨hi_notin, his_nodup⟩
      rw [t9s1_prepCirc, t9s1_unitary_append, ← Matrix.mulVec_mulVec, t9s1_lift1_unitary,
        t9s1_embedOp_mulVec_prodVec, ih his_nodup]
      congr 1
      funext q
      rcases Equiv.surjective finSumFinEquiv q with ⟨s, rfl⟩
      simp only [Equiv.symm_apply_apply]
      rcases s with j | k
      · simp only [finSumFinEquiv_apply_left, List.mem_cons]
        by_cases hj : j = i
        · subst hj
          simp [hi_notin]
        · have hne : Fin.castAdd M j ≠ Fin.castAdd M i := by
            intro h
            apply hj
            exact Fin.castAdd_injective L M h
          simp [hj]
      · have hne : Fin.natAdd L k ≠ Fin.castAdd M i := by
          intro h
          have hi : (i : ℕ) < L := i.isLt
          have heq : L + (k : ℕ) = (i : ℕ) := by
            simpa [Fin.val_natAdd, Fin.val_castAdd] using congrArg Fin.val h
          omega
        simp [finSumFinEquiv_apply_right, Function.update_of_ne hne]

private theorem t9s1_ket0Anc_eq_prodVec (N : ℕ) :
    t9_ket0Anc N = t9s1_prodVec (fun _ => basisVec false) := by
  funext z
  simp only [t9_ket0Anc, t9s1_prodVec, basisVec]
  by_cases hz : z = fun _ => false
  · subst hz; simp
  · rw [if_neg hz]
    have hnot : ∃ q : Fin N, z q ≠ false := by
      by_contra hall
      push Not at hall
      exact hz (funext hall)
    rcases hnot with ⟨q, hq⟩
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)

private theorem t9s1_prodVec_split {L M : ℕ} (g : Fin L → Bool → ℂ) (h : Fin M → Bool → ℂ)
    (z : Qubits (L + M)) :
    t9s1_prodVec (fun q => match finSumFinEquiv.symm q with
      | Sum.inl i => g i
      | Sum.inr j => h j) z =
      (∏ i : Fin L, g i (z (Fin.castAdd M i))) * (∏ j : Fin M, h j (z (Fin.natAdd L j))) := by
  dsimp only [t9s1_prodVec]
  rw [← Fintype.prod_equiv finSumFinEquiv (fun s => match s with
    | Sum.inl i => g i (z (Fin.castAdd M i))
    | Sum.inr j => h j (z (Fin.natAdd L j))) _ (fun s => by
      cases s <;> simp [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right])]
  rw [Fintype.prod_sum_type]

private theorem t9s1_qubits_split_sum {L M : ℕ} (F : Qubits L → Qubits M → ℝ) :
    (∑ z : Qubits (L + M), F (fun i => z (Fin.castAdd M i)) (fun j => z (Fin.natAdd L j))) =
      ∑ x : Qubits L, ∑ y : Qubits M, F x y := by
  rw [← Fintype.sum_equiv (t9s1_appendEquiv L M) (fun p => F p.1 p.2) _ (fun p => by
    simp [t9s1_appendEquiv, Fin.append_left, Fin.append_right])]
  rw [Fintype.sum_prod_type]

private theorem t9s1_sum_sq_prod {N : ℕ} (f : Fin N → Bool → ℂ) :
    (∑ z : Qubits N, ‖t9s1_prodVec f z‖ ^ 2) = ∏ q : Fin N, ∑ b : Bool, ‖f q b‖ ^ 2 := by
  have h1 : ∀ z : Qubits N, ‖t9s1_prodVec f z‖ ^ 2 = ∏ q : Fin N, ‖f q (z q)‖ ^ 2 := by
    intro z
    simp only [t9s1_prodVec, norm_prod, Finset.prod_pow]
  simp_rw [h1]
  exact (Fintype.prod_sum fun q b => ‖f q b‖ ^ 2).symm

private theorem t9s1_norm_sq_basisVec_false :
    ∑ b : Bool, ‖basisVec false b‖ ^ 2 = 1 := by
  simp [basisVec]

private theorem t9s1_norm_sq_resourceVec (θ : ℝ) :
    ∑ b : Bool, ‖resourceVec θ b‖ ^ 2 = 1 := by
  have h1 : (∑ b : Bool, ‖resourceVec θ b‖ ^ 2) =
      ‖resourceVec θ false‖ ^ 2 + ‖resourceVec θ true‖ ^ 2 := by
    rw [Fintype.sum_bool, add_comm]
  rw [h1]
  have hf : resourceVec θ false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    simp [resourceVec, rot, plusVec, Matrix.mulVec, dotProduct]
  have ht : resourceVec θ true = Complex.exp ((θ : ℂ) * Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    simp [resourceVec, rot, plusVec, Matrix.mulVec, dotProduct]
  rw [hf, ht, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), inv_pow,
    Real.sq_sqrt (by norm_num)]
  have hhalf : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  exact hhalf

private theorem t9s1_hadamard_mulVec_basisVec_false :
    hadamard.mulVec (basisVec false) = plusVec := by
  ext b
  cases b <;> simp [hadamard, basisVec, plusVec, Matrix.mulVec, dotProduct]

private theorem t9s1_euclidean_sqrt_sum_le {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Real.sqrt (∑ i : ι, ‖u i + v i‖ ^ 2) ≤
      Real.sqrt (∑ i : ι, ‖u i‖ ^ 2) + Real.sqrt (∑ i : ι, ‖v i‖ ^ 2) := by
  have hnorm : ∀ w : ι → ℂ, Real.sqrt (∑ i : ι, ‖w i‖ ^ 2) = ‖WithLp.toLp 2 w‖ := by
    intro w
    rw [← EuclideanSpace.norm_sq_eq (WithLp.toLp 2 w), Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm (fun i => u i + v i), hnorm u, hnorm v]
  exact norm_add_le (WithLp.toLp 2 u) (WithLp.toLp 2 v)

private theorem t9s1_prod_l2_telescope : ∀ (k : ℕ) (a b : Fin k → Bool → ℂ) {ε : ℝ},
    0 ≤ ε →
    (∀ i : Fin k, (∑ c : Bool, ‖a i c‖ ^ 2) = 1) →
    (∀ i : Fin k, (∑ c : Bool, ‖b i c‖ ^ 2) = 1) →
    (∀ i : Fin k, Real.sqrt (∑ c : Bool, ‖a i c - b i c‖ ^ 2) ≤ ε) →
    Real.sqrt (∑ x : Qubits k,
      ‖(∏ i : Fin k, a i (x i)) - (∏ i : Fin k, b i (x i))‖ ^ 2) ≤ (k : ℝ) * ε
  | 0, a, b, ε, hε, _, _, _ => by
      simp
  | k + 1, a, b, ε, hε, ha, hb, hdist => by
      let a' : Fin k → Bool → ℂ := fun i => a i.succ
      let b' : Fin k → Bool → ℂ := fun i => b i.succ
      have ih := t9s1_prod_l2_telescope k a' b' hε
        (fun i => ha i.succ) (fun i => hb i.succ) (fun i => hdist i.succ)
      let splitEquiv : Bool × Qubits k ≃ Qubits (k + 1) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun x => (x 0, Fin.tail x)
          left_inv := fun p => by ext <;> simp [Fin.cons, Fin.tail]
          right_inv := fun x => by
            funext i
            cases i using Fin.cases with
            | zero => simp [Fin.cons]
            | succ j => simp [Fin.cons, Fin.tail] }
      have hsum_split : (∑ x : Qubits (k + 1),
          ‖(∏ i : Fin (k + 1), a i (x i)) - (∏ i : Fin (k + 1), b i (x i))‖ ^ 2) =
          ∑ p : Bool × Qubits k,
            ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i)) +
              b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2 := by
        rw [← Fintype.sum_equiv splitEquiv (fun p =>
          ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i)) +
            b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2)
          _ (fun p => by
            dsimp only [splitEquiv, Equiv.coe_fn_mk, a', b']
            rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact congrArg (fun r : ℝ => r ^ 2) (congrArg norm (by ring)))]
      rw [hsum_split]
      have htri := t9s1_euclidean_sqrt_sum_le
        (fun p : Bool × Qubits k => (a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i)))
        (fun p : Bool × Qubits k => b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i))))
      have hterm1 : Real.sqrt (∑ p : Bool × Qubits k,
          ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i))‖ ^ 2) ≤ ε := by
        have hfac : (∑ p : Bool × Qubits k,
            ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i))‖ ^ 2) =
            (∑ c : Bool, ‖a 0 c - b 0 c‖ ^ 2) *
              (∑ x' : Qubits k, ‖∏ i : Fin k, a' i (x' i)‖ ^ 2) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => by rw [norm_mul, mul_pow]
        have ha'_norm : (∑ x' : Qubits k, ‖∏ i : Fin k, a' i (x' i)‖ ^ 2) = 1 := by
          have h := t9s1_sum_sq_prod a'
          simp only [t9s1_prodVec] at h
          rw [h]
          exact Finset.prod_eq_one fun i _ => ha i.succ
        rw [hfac, ha'_norm, mul_one]
        exact hdist 0
      have hterm2 : Real.sqrt (∑ p : Bool × Qubits k,
          ‖b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2) ≤
          (k : ℝ) * ε := by
        have hfac : (∑ p : Bool × Qubits k,
            ‖b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2) =
            (∑ c : Bool, ‖b 0 c‖ ^ 2) *
              (∑ x' : Qubits k, ‖(∏ i : Fin k, a' i (x' i)) - (∏ i : Fin k, b' i (x' i))‖ ^ 2) := by
          rw [Fintype.sum_prod_type, Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x' _ => by rw [norm_mul, mul_pow]
        rw [hfac, hb 0, one_mul]
        exact ih
      calc Real.sqrt (∑ p : Bool × Qubits k,
            ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i)) +
              b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2)
          ≤ Real.sqrt (∑ p : Bool × Qubits k,
              ‖(a 0 p.1 - b 0 p.1) * (∏ i : Fin k, a' i (p.2 i))‖ ^ 2) +
            Real.sqrt (∑ p : Bool × Qubits k,
              ‖b 0 p.1 * ((∏ i : Fin k, a' i (p.2 i)) - (∏ i : Fin k, b' i (p.2 i)))‖ ^ 2) := htri
        _ ≤ ε + (k : ℝ) * ε := add_le_add hterm1 hterm2
        _ = ((k + 1 : ℕ) : ℝ) * ε := by push_cast; ring

private theorem t9s1_prep_resource_states {C_RS ε₀ : ℝ} (_hC_RS : 0 < C_RS) (hε₀ : 0 < ε₀)
    (hRS : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ k : ℕ, (k = 1 ∨ k = 2) →
        ∀ U : Matrix (Qubits k) (Qubits k) ℂ,
          U ∈ Matrix.unitaryGroup (Qubits k) ℂ →
          ∃ c : Circuit CliffordT k,
            (c.size : ℝ) ≤ C_RS * Real.log (1 / ε) ∧
            ApproxUpToPhase U c.unitary ε)
    (L M : ℕ) (hL : 1 ≤ L) (α : Fin L → ℝ) {δ_tot : ℝ} (hδ : 0 < δ_tot) :
    ∃ (cPrep : Circuit CliffordT (L + M)) (Φ : ℝ),
      (cPrep.size : ℝ) ≤ (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) ∧
      (∑ z : Qubits (L + M), ‖(cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z‖ ^ 2) = 1 ∧
      (∑ z : Qubits (L + M), ‖t9_productAncVec α z‖ ^ 2) = 1 ∧
      Real.sqrt (∑ z : Qubits (L + M),
        ‖Complex.exp ((Φ : ℂ) * Complex.I) *
          (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z -
          t9_productAncVec α z‖ ^ 2) ≤ δ_tot := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hL
  let ε_s : ℝ := min (ε₀ / 2) (δ_tot / (2 * (L : ℝ)))
  have hε_pos : 0 < ε_s := lt_min (by positivity) (by positivity)
  have hε_lt : ε_s < ε₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀)
  have hinv_eq : 1 / ε_s = max (2 / ε₀) (2 * (L : ℝ) / δ_tot) := by
    have h1 : 1 / (ε₀ / 2) = 2 / ε₀ := by field_simp
    have h2 : 1 / (δ_tot / (2 * (L : ℝ))) = 2 * (L : ℝ) / δ_tot := by field_simp
    dsimp [ε_s]
    rcases le_total (ε₀ / 2) (δ_tot / (2 * (L : ℝ))) with h | h
    · rw [min_eq_left h, h1]
      symm
      apply max_eq_left
      rw [← h1, ← h2]
      exact one_div_le_one_div_of_le (by positivity) h
    · rw [min_eq_right h, h2]
      symm
      apply max_eq_right
      rw [← h1, ← h2]
      exact one_div_le_one_div_of_le (by positivity) h
  let U_target : Fin L → Matrix (Qubits 1) (Qubits 1) ℂ :=
    fun i => (Gate.ofMatrix1 (rot (α i) * hadamard)).mat
  have hU_mem : ∀ i : Fin L, U_target i ∈ Matrix.unitaryGroup (Qubits 1) ℂ := fun i =>
    t9s1_ofMatrix1_isUnitary (mul_mem (t9s1_rot_mem_unitary (α i)) t9s1_hadamard_mem_unitary)
  have hRS_i : ∀ i : Fin L, ∃ c : Circuit CliffordT 1,
      (c.size : ℝ) ≤ C_RS * Real.log (1 / ε_s) ∧ ApproxUpToPhase (U_target i) c.unitary ε_s :=
    fun i => hRS ε_s hε_pos hε_lt 1 (Or.inl rfl) (U_target i) (hU_mem i)
  let c : Fin L → Circuit CliffordT 1 := fun i => Classical.choose (hRS_i i)
  have hc_size : ∀ i : Fin L, ((c i).size : ℝ) ≤ C_RS * Real.log (1 / ε_s) :=
    fun i => (Classical.choose_spec (hRS_i i)).1
  have hc_approx : ∀ i : Fin L, ApproxUpToPhase (U_target i) (c i).unitary ε_s :=
    fun i => (Classical.choose_spec (hRS_i i)).2
  let θ : Fin L → ℝ := fun i => Classical.choose (hc_approx i)
  have hθ_spec : ∀ i : Fin L,
      specNorm (U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) ≤ ε_s :=
    fun i => Classical.choose_spec (hc_approx i)
  let cPrep : Circuit CliffordT (L + M) := t9s1_prepCirc c (List.finRange L)
  let Φ : ℝ := ∑ i : Fin L, θ i
  refine ⟨cPrep, Φ, ?_, ?_, ?_, ?_⟩
  · have hsz : (cPrep.size : ℝ) = ∑ i : Fin L, ((c i).size : ℝ) := by
      dsimp [cPrep]
      rw [t9s1_prepCirc_size, Nat.cast_list_sum, List.map_map]
      simp only [Function.comp_def]
      rw [← Fin.sum_univ_def (fun i : Fin L => ((c i).size : ℝ))]
    rw [hsz, ← hinv_eq]
    calc ∑ i : Fin L, ((c i).size : ℝ)
        ≤ ∑ _ : Fin L, C_RS * Real.log (1 / ε_s) := Finset.sum_le_sum fun i _ => hc_size i
      _ = (L : ℝ) * (C_RS * Real.log (1 / ε_s)) := by simp
  · let ketTarget : Fin (L + M) → Bool → ℂ := fun q =>
      match finSumFinEquiv.symm q with
      | Sum.inl i => t9s1_applyOnWire (c i).unitary (basisVec false)
      | Sum.inr _ => basisVec false
    have hmul_ket : cPrep.unitary.mulVec (t9_ket0Anc (L + M)) = t9s1_prodVec ketTarget := by
      dsimp [cPrep, ketTarget]
      rw [t9s1_ket0Anc_eq_prodVec, t9s1_prepCirc_mulVec c (List.finRange L) (List.nodup_finRange L)]
      congr 1; funext q
      rcases finSumFinEquiv.symm q with i | j
      · simp [List.mem_finRange]
      · rfl
    have hwire_norm : ∀ i : Fin L,
        (∑ b : Bool, ‖t9s1_applyOnWire (c i).unitary (basisVec false) b‖ ^ 2) = 1 := by
      intro i
      let ψ₀ : EuclideanSpace ℂ (Qubits 1) := WithLp.toLp 2 (t9_ket0Anc 1)
      have hψ₀_sq : ‖ψ₀‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        rw [Finset.sum_eq_single (fun _ : Fin 1 => false)]
        · simp [ψ₀, t9_ket0Anc]
        · intro v _ hv; simp [ψ₀, t9_ket0Anc, hv]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hψ₀ : ‖ψ₀‖ = 1 := by
        rw [← Real.sqrt_sq (norm_nonneg ψ₀), hψ₀_sq, Real.sqrt_one]
      have hU_c : (c i).unitary ∈ Matrix.unitaryGroup (Qubits 1) ℂ :=
        t9s1_circuit_unitary_mem_unitary t9s1_cliffordT_isUnitary (c i)
      have hact : ‖act (c i).unitary ψ₀‖ = 1 := by
        rw [act_norm_of_mem_unitaryGroup hU_c ψ₀, hψ₀]
      have hsq : ‖act (c i).unitary ψ₀‖ ^ 2 = 1 := by rw [hact, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at hsq
      have heq_vec : ∀ u : Qubits 1,
          (act (c i).unitary ψ₀).ofLp u =
            t9s1_applyOnWire (c i).unitary (basisVec false) (u 0) := by
        intro u
        have hu : (fun _ : Fin 1 => u 0) = u := funext fun k => by rw [Fin.eq_zero k]
        have hket1 : (fun v : Qubits 1 => basisVec false (v 0)) = t9_ket0Anc 1 := by
          funext v
          simp only [basisVec, t9_ket0Anc]
          split_ifs with h1 h2 h2
          · rfl
          · exfalso; apply h2; funext k; rw [Fin.eq_zero k]; exact h1
          · exfalso; apply h1; rw [h2]
          · rfl
        simp only [act, ψ₀, t9s1_applyOnWire, hket1, hu]
      simp_rw [heq_vec] at hsq
      rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _
        (fun b => ‖t9s1_applyOnWire (c i).unitary (basisVec false) b‖ ^ 2)
        (fun u => rfl)]
      exact hsq
    rw [hmul_ket, t9s1_sum_sq_prod]
    refine Finset.prod_eq_one fun q _ => ?_
    dsimp only [ketTarget]
    rcases finSumFinEquiv.symm q with i | j
    · exact hwire_norm i
    · exact t9s1_norm_sq_basisVec_false
  · let prodTarget : Fin (L + M) → Bool → ℂ := fun q =>
      match finSumFinEquiv.symm q with
      | Sum.inl i => resourceVec (α i)
      | Sum.inr _ => basisVec false
    have hprod_eq : t9_productAncVec α = t9s1_prodVec prodTarget := by
      funext z
      exact (t9s1_prodVec_split (fun i => resourceVec (α i)) (fun _ => basisVec false) z).symm
    rw [hprod_eq, t9s1_sum_sq_prod]
    refine Finset.prod_eq_one fun q _ => ?_
    dsimp only [prodTarget]
    rcases finSumFinEquiv.symm q with i | j
    · exact t9s1_norm_sq_resourceVec (α i)
    · exact t9s1_norm_sq_basisVec_false
  · let v_i : Fin L → Bool → ℂ := fun i => t9s1_applyOnWire (c i).unitary (basisVec false)
    let v'_i : Fin L → Bool → ℂ := fun i b => Complex.exp ((θ i : ℂ) * Complex.I) * v_i i b
    let ketTarget' : Fin (L + M) → Bool → ℂ := fun q =>
      match finSumFinEquiv.symm q with
      | Sum.inl i => v_i i
      | Sum.inr _ => basisVec false
    have hmul_ket : cPrep.unitary.mulVec (t9_ket0Anc (L + M)) = t9s1_prodVec ketTarget' := by
      dsimp [cPrep, ketTarget']
      rw [t9s1_ket0Anc_eq_prodVec, t9s1_prepCirc_mulVec c (List.finRange L) (List.nodup_finRange L)]
      congr 1; funext q
      rcases finSumFinEquiv.symm q with i | j
      · simp [List.mem_finRange, v_i]
      · rfl
    have hphase_prod : ∀ z : Qubits (L + M),
        Complex.exp ((Φ : ℂ) * Complex.I) *
          (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z =
          (∏ i : Fin L, v'_i i (z (Fin.castAdd M i))) *
            (∏ j : Fin M, basisVec false (z (Fin.natAdd L j))) := by
      intro z
      rw [hmul_ket]
      dsimp only [ketTarget']
      rw [t9s1_prodVec_split]
      have hexp : Complex.exp ((Φ : ℂ) * Complex.I) =
          ∏ i : Fin L, Complex.exp ((θ i : ℂ) * Complex.I) := by
        dsimp [Φ]
        rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      rw [hexp, ← mul_assoc, ← Finset.prod_mul_distrib]
    have hsum_split : (∑ z : Qubits (L + M),
        ‖Complex.exp ((Φ : ℂ) * Complex.I) *
          (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z -
          t9_productAncVec α z‖ ^ 2) =
        ∑ x : Qubits L,
          ‖(∏ i : Fin L, v'_i i (x i)) - (∏ i : Fin L, resourceVec (α i) (x i))‖ ^ 2 := by
      have hterm : ∀ z : Qubits (L + M),
          ‖Complex.exp ((Φ : ℂ) * Complex.I) *
            (cPrep.unitary.mulVec (t9_ket0Anc (L + M))) z -
            t9_productAncVec α z‖ ^ 2 =
            ‖(∏ i : Fin L, v'_i i (z (Fin.castAdd M i))) -
              (∏ i : Fin L, resourceVec (α i) (z (Fin.castAdd M i)))‖ ^ 2 *
            ‖∏ j : Fin M, basisVec false (z (Fin.natAdd L j))‖ ^ 2 := by
        intro z
        rw [hphase_prod z]
        dsimp [t9_productAncVec]
        rw [← sub_mul, norm_mul, mul_pow]
      simp_rw [hterm]
      rw [t9s1_qubits_split_sum (fun x y =>
        ‖(∏ i : Fin L, v'_i i (x i)) - (∏ i : Fin L, resourceVec (α i) (x i))‖ ^ 2 *
          ‖∏ j : Fin M, basisVec false (y j)‖ ^ 2)]
      have hM_norm : (∑ y : Qubits M, ‖∏ j : Fin M, basisVec false (y j)‖ ^ 2) = 1 := by
        have h := t9s1_sum_sq_prod (fun _ : Fin M => basisVec false)
        simp only [t9s1_prodVec] at h
        rw [h]
        exact Finset.prod_eq_one fun _ _ => t9s1_norm_sq_basisVec_false
      simp_rw [← Finset.mul_sum, hM_norm, mul_one]
    have hv'_norm : ∀ i : Fin L, (∑ b : Bool, ‖v'_i i b‖ ^ 2) = 1 := by
      intro i
      have hU_c : (c i).unitary ∈ Matrix.unitaryGroup (Qubits 1) ℂ :=
        t9s1_circuit_unitary_mem_unitary t9s1_cliffordT_isUnitary (c i)
      let ψ₀ : EuclideanSpace ℂ (Qubits 1) := WithLp.toLp 2 (t9_ket0Anc 1)
      have hψ₀_sq : ‖ψ₀‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        rw [Finset.sum_eq_single (fun _ : Fin 1 => false)]
        · simp [ψ₀, t9_ket0Anc]
        · intro v _ hv; simp [ψ₀, t9_ket0Anc, hv]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hψ₀ : ‖ψ₀‖ = 1 := by
        rw [← Real.sqrt_sq (norm_nonneg ψ₀), hψ₀_sq, Real.sqrt_one]
      have hsq : ‖act (c i).unitary ψ₀‖ ^ 2 = 1 := by
        rw [act_norm_of_mem_unitaryGroup hU_c ψ₀, hψ₀, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at hsq
      have heq_vec : ∀ u : Qubits 1,
          ‖(act (c i).unitary ψ₀).ofLp u‖ ^ 2 = ‖v'_i i (u 0)‖ ^ 2 := by
        intro u
        have hu : (fun _ : Fin 1 => u 0) = u := funext fun k => by rw [Fin.eq_zero k]
        have hket1 : (fun v : Qubits 1 => basisVec false (v 0)) = t9_ket0Anc 1 := by
          funext v
          simp only [basisVec, t9_ket0Anc]
          split_ifs with h1 h2 h2
          · rfl
          · exfalso; apply h2; funext k; rw [Fin.eq_zero k]; exact h1
          · exfalso; apply h1; rw [h2]
          · rfl
        have hval : (act (c i).unitary ψ₀).ofLp u = v_i i (u 0) := by
          simp only [act, ψ₀, v_i, t9s1_applyOnWire, hket1, hu]
        rw [hval]
        simp [v'_i, Complex.norm_exp_ofReal_mul_I]
      simp_rw [heq_vec] at hsq
      rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _
        (fun b => ‖v'_i i b‖ ^ 2) (fun u => rfl)]
      exact hsq
    have hv'_dist : ∀ i : Fin L,
        Real.sqrt (∑ b : Bool, ‖v'_i i b - resourceVec (α i) b‖ ^ 2) ≤ ε_s := by
      intro i
      let ψ₀ : EuclideanSpace ℂ (Qubits 1) := WithLp.toLp 2 (t9_ket0Anc 1)
      have hψ₀_sq : ‖ψ₀‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        rw [Finset.sum_eq_single (fun _ : Fin 1 => false)]
        · simp [ψ₀, t9_ket0Anc]
        · intro v _ hv; simp [ψ₀, t9_ket0Anc, hv]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hψ₀ : ‖ψ₀‖ = 1 := by
        rw [← Real.sqrt_sq (norm_nonneg ψ₀), hψ₀_sq, Real.sqrt_one]
      have hmul := @Matrix.l2_opNorm_mulVec ℂ (Qubits 1) (Qubits 1) _ _ _ _
        (U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) ψ₀
      have hle : ‖(EuclideanSpace.equiv (Qubits 1) ℂ).symm
          ((U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) *ᵥ ψ₀.ofLp)‖ ≤ ε_s := by
        calc _ ≤ specNorm (U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) * ‖ψ₀‖ := hmul
          _ = specNorm (U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) := by
              rw [hψ₀, mul_one]
          _ ≤ ε_s := hθ_spec i
      have hket1 : (fun v : Qubits 1 => basisVec false (v 0)) = t9_ket0Anc 1 := by
        funext v
        simp only [basisVec, t9_ket0Anc]
        split_ifs with h1 h2 h2
        · rfl
        · exfalso; apply h2; funext k; rw [Fin.eq_zero k]; exact h1
        · exfalso; apply h1; rw [h2]
        · rfl
      have hU_vec : ∀ u : Qubits 1,
          ((U_target i).mulVec (t9_ket0Anc 1)) u = resourceVec (α i) (u 0) := by
        intro u
        have h1 : ((U_target i).mulVec (t9_ket0Anc 1)) u =
            ((rot (α i) * hadamard).mulVec (basisVec false)) (u 0) := by
          simp only [U_target, Gate.ofMatrix1, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
            t9_ket0Anc, basisVec]
          rw [Finset.sum_eq_single (fun _ : Fin 1 => false)]
          · rw [Finset.sum_eq_single false]
            · simp
            · intro b _ hb; simp [hb]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro v _ hv; simp [hv]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [h1, ← Matrix.mulVec_mulVec, t9s1_hadamard_mulVec_basisVec_false]
        rfl
      have hsq : ∑ b : Bool, ‖v'_i i b - resourceVec (α i) b‖ ^ 2 ≤ ε_s ^ 2 := by
        have hsq' := pow_le_pow_left₀ (norm_nonneg _) hle 2
        rw [EuclideanSpace.norm_sq_eq] at hsq'
        have hvec_eq : ∀ u : Qubits 1,
            ‖((EuclideanSpace.equiv (Qubits 1) ℂ).symm
              ((U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) *ᵥ ψ₀.ofLp)).ofLp u‖ ^ 2 =
              ‖v'_i i (u 0) - resourceVec (α i) (u 0)‖ ^ 2 := by
          intro u
          have hu : (fun _ : Fin 1 => u 0) = u := funext fun k => by rw [Fin.eq_zero k]
          have hsub : ((U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) *ᵥ ψ₀.ofLp) u =
              resourceVec (α i) (u 0) - v'_i i (u 0) := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec]
            change ((U_target i).mulVec (t9_ket0Anc 1)) u -
                Complex.exp ((θ i : ℂ) * Complex.I) * ((c i).unitary.mulVec (t9_ket0Anc 1)) u =
              resourceVec (α i) (u 0) - v'_i i (u 0)
            rw [hU_vec u]
            simp only [v'_i, v_i, t9s1_applyOnWire, hket1, hu]
          change ‖((U_target i - Complex.exp ((θ i : ℂ) * Complex.I) • (c i).unitary) *ᵥ ψ₀.ofLp) u‖ ^ 2 = _
          rw [hsub, norm_sub_rev]
        simp_rw [hvec_eq] at hsq'
        rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Bool) _
          (fun b => ‖v'_i i b - resourceVec (α i) b‖ ^ 2) (fun u => rfl)]
        exact hsq'
      calc Real.sqrt (∑ b : Bool, ‖v'_i i b - resourceVec (α i) b‖ ^ 2)
          ≤ Real.sqrt (ε_s ^ 2) := Real.sqrt_le_sqrt hsq
        _ = ε_s := Real.sqrt_sq hε_pos.le
    rw [hsum_split]
    calc Real.sqrt (∑ x : Qubits L,
          ‖(∏ i : Fin L, v'_i i (x i)) - (∏ i : Fin L, resourceVec (α i) (x i))‖ ^ 2)
        ≤ (L : ℝ) * ε_s :=
          t9s1_prod_l2_telescope L v'_i (fun i => resourceVec (α i)) hε_pos.le
            hv'_norm (fun i => t9s1_norm_sq_resourceVec (α i)) hv'_dist
      _ ≤ (L : ℝ) * (δ_tot / (2 * (L : ℝ))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hLpos.le
      _ = δ_tot / 2 := by field_simp
      _ ≤ δ_tot := half_le_self hδ.le

end Thm9Step1Helpers

theorem t9_step1_api : Thm9Step1API where
  cliffordT_isUnitary := t9s1_cliffordT_isUnitary
  traceDist_self := t9s1_traceDist_self
  traceNorm_add_le := t9s1_traceNorm_add_le
  traceDist_triangle := t9s1_traceDist_triangle
  traceNorm_smul_of_nonneg := t9s1_traceNorm_smul_of_nonneg
  isDensityOperator_conj_unitary := t9s1_isDensityOperator_conj_unitary
  cptp_traceNorm_le := t9s1_cptp_traceNorm_le
  proj_decomp_density := t9s1_proj_decomp_density
  traceDist_density_le_two := t9s1_traceDist_density_le_two
  isHermitian_channelRef := t9s1_channelRef_isHermitian
  dataChannelRef_eq := t9s1_dataChannelRef_eq
  prependAnc_dataChannelRef := t9s1_prependAnc_dataChannelRef
  isHermitian_partialTraceAnc := t9s1_isHermitian_partialTraceAnc
  partialTraceAnc_traceNorm_le := t9s1_partialTraceAnc_traceNorm_le
  isDensityOperator_tensorAncVec := t9s1_isDensityOperator_tensorAncVec
  isDensityOperator_partialTraceAnc := t9s1_isDensityOperator_partialTraceAnc
  channelWithAnc_approx_le := t9s1_channelWithAnc_approx_le
  prep_resource_states := t9s1_prep_resource_states

section Thm9Step2Helpers

open QAlgorithms ConstOverheadCompile.Main

/-! ### Norm-square identities -/

private theorem norm_sq_basisVec_aux (b : Bool) :
    ‖basisVec b false‖ ^ 2 + ‖basisVec b true‖ ^ 2 = 1 := by
  cases b <;> simp [basisVec]

private theorem norm_sq_plusVec_aux :
    ‖plusVec false‖ ^ 2 + ‖plusVec true‖ ^ 2 = 1 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  simp only [plusVec, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [inv_pow, Real.sq_sqrt h2]
  norm_num

private theorem resourceVec_false (θ : ℝ) :
    resourceVec θ false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [resourceVec, rot, plusVec, Matrix.mulVec, dotProduct]

private theorem resourceVec_true (θ : ℝ) :
    resourceVec θ true = Complex.exp ((θ : ℂ) * Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [resourceVec, rot, plusVec, Matrix.mulVec, dotProduct]

private theorem norm_sq_resourceVec_aux (θ : ℝ) :
    ‖resourceVec θ false‖ ^ 2 + ‖resourceVec θ true‖ ^ 2 = 1 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [resourceVec_false, resourceVec_true]
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [inv_pow, Real.sq_sqrt h2]
  norm_num

private theorem sum_bool_mul_star {v : Bool → ℂ} (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1) :
    (∑ b : Bool, v b * star (v b)) = 1 := by
  rw [Fintype.sum_bool]
  have hmul : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    change z * starRingEnd ℂ z = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmul (v false), hmul (v true), ← Complex.ofReal_add, add_comm, hv, Complex.ofReal_one]

/-! ### Wire manipulation and pure-wire lemmas -/

private theorem setWire_self {N : ℕ} (q : Fin N) (b : Bool) (x : Qubits N) :
    t9_setWire q b x q = b := by
  dsimp only [t9_setWire]
  exact Function.update_self q b x

private theorem setWire_of_ne {N : ℕ} {q a : Fin N} (h : a ≠ q) (b : Bool) (x : Qubits N) :
    t9_setWire q b x a = x a := by
  dsimp only [t9_setWire]
  exact Function.update_of_ne h b x

private theorem setWire_idem {N : ℕ} (q : Fin N) (b b' : Bool) (x : Qubits N) :
    t9_setWire q b (t9_setWire q b' x) = t9_setWire q b x := by
  funext a
  by_cases ha : a = q <;> simp [t9_setWire, ha]

private theorem setWire_comm {N : ℕ} {q q' : Fin N} (h : q ≠ q') (b b' : Bool) (x : Qubits N) :
    t9_setWire q b (t9_setWire q' b' x) = t9_setWire q' b' (t9_setWire q b x) := by
  funext a
  by_cases haq : a = q
  · subst haq; simp [t9_setWire, h]
  · by_cases haq' : a = q'
    · subst haq'; simp [t9_setWire, h.symm]
    · simp [t9_setWire, haq, haq']

private theorem setWire_eq_self {N : ℕ} (q : Fin N) (x : Qubits N) :
    t9_setWire q (x q) x = x := by
  dsimp only [t9_setWire]
  exact Function.update_eq_self q x

private def swapBit {N : ℕ} (q : Fin N) (c d : Bool) (x : Qubits N) : Qubits N :=
  t9_setWire q (if x q = c then d else if x q = d then c else x q) x

private theorem swapBit_invol {N : ℕ} (q : Fin N) (c d : Bool) (x : Qubits N) :
    swapBit q c d (swapBit q c d x) = x := by
  funext a
  by_cases ha : a = q
  · subst ha
    cases hx : x a <;> cases c <;> cases d <;> simp [swapBit, setWire_self, hx]
  · simp [swapBit, setWire_of_ne ha]

private theorem swapBit_apply_of_ne {N : ℕ} {q a : Fin N} (h : a ≠ q) (c d : Bool) (x : Qubits N) :
    swapBit q c d x a = x a :=
  setWire_of_ne h _ x

private theorem swapBit_apply_eq_iff {N : ℕ} (q : Fin N) (c d : Bool) (x : Qubits N) :
    swapBit q c d x q = d ↔ x q = c := by
  simp only [swapBit, setWire_self]
  cases hxc : x q <;> cases hc : c <;> cases hd : d <;> simp

private theorem setWire_swapBit_of_eq {N : ℕ} (q : Fin N) (c d : Bool) {x : Qubits N}
    (hx : x q = c) :
    t9_setWire q c (swapBit q c d x) = x := by
  funext a
  by_cases ha : a = q
  · subst ha; simp [setWire_self, hx]
  · simp [setWire_of_ne ha, swapBit_apply_of_ne ha]

private theorem hasPureWire_traceAndSet_self_aux {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ)
    (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_HasPureWire q v (t9_traceAndSetWire q v σ) := by
  ext p₁ p₂
  simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_self, setWire_idem]
  have hsum : (∑ b : Bool, (∑ b' : Bool, σ (p₁.1, t9_setWire q b' p₁.2) (p₂.1, t9_setWire q b' p₂.2)) *
      v b * star (v b)) =
      (∑ b' : Bool, σ (p₁.1, t9_setWire q b' p₁.2) (p₂.1, t9_setWire q b' p₂.2)) *
        (∑ b : Bool, v b * star (v b)) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hsum, sum_bool_mul_star hv, mul_one]

private theorem hasPureWire_traceAndSet_other_aux {N m_ref : ℕ} {q q' : Fin N} (hq : q ≠ q')
    (v u : Bool → ℂ)
    {σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ}
    (hσ : t9_HasPureWire q' u σ) :
    t9_HasPureWire q' u (t9_traceAndSetWire q v σ) := by
  ext p₁ p₂
  simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_of_ne hq]
  have h1 : ∀ b b' : Bool,
      σ (p₁.1, t9_setWire q b (t9_setWire q' b' p₁.2))
        (p₂.1, t9_setWire q b (t9_setWire q' b' p₂.2)) =
      σ (p₁.1, t9_setWire q' b' (t9_setWire q b p₁.2))
        (p₂.1, t9_setWire q' b' (t9_setWire q b p₂.2)) := by
    intro b b'
    rw [setWire_comm hq, setWire_comm hq]
  simp_rw [h1, ← Finset.sum_mul]
  have h2 : ∀ b : Bool,
      (∑ b' : Bool, σ (p₁.1, t9_setWire q' b' (t9_setWire q b p₁.2))
        (p₂.1, t9_setWire q' b' (t9_setWire q b p₂.2))) *
          u (p₁.2 q') * star (u (p₂.2 q')) =
      σ (p₁.1, t9_setWire q b p₁.2) (p₂.1, t9_setWire q b p₂.2) := by
    intro b
    have := congrFun (congrFun hσ (p₁.1, t9_setWire q b p₁.2)) (p₂.1, t9_setWire q b p₂.2)
    simpa [t9_traceAndSetWire, setWire_of_ne hq.symm] using this
  have hsum : (∑ x : Bool, (∑ y : Bool, σ (p₁.1, t9_setWire q' x (t9_setWire q y p₁.2))
        (p₂.1, t9_setWire q' x (t9_setWire q y p₂.2)))) *
      v (p₁.2 q) * star (v (p₂.2 q)) * u (p₁.2 q') * star (u (p₂.2 q')) =
      (∑ y : Bool, (∑ x : Bool, σ (p₁.1, t9_setWire q' x (t9_setWire q y p₁.2))
        (p₂.1, t9_setWire q' x (t9_setWire q y p₂.2))) * u (p₁.2 q') * star (u (p₂.2 q'))) *
      v (p₁.2 q) * star (v (p₂.2 q)) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => by ring))
  rw [hsum]
  simp_rw [h2]

private theorem hasPureWire_tensorAncVec_of_factor {n a m_ref : ℕ}
    (k : Fin a) (v : Bool → ℂ) (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1)
    (χ : Qubits a → ℂ) (rest : Qubits a → ℂ)
    (hχ : ∀ z, χ z = v (z k) * rest z)
    (hrest : ∀ b z, rest (t9_setWire k b z) = rest z)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    t9_HasPureWire (Fin.natAdd n k) v (t9_tensorAncVec χ ρ) := by
  ext p₁ p₂
  simp only [t9_traceAndSetWire, t9_tensorAncVec, Matrix.of_apply]
  have hcast : ∀ b (x : Qubits (n + a)) (i : Fin n),
      t9_setWire (Fin.natAdd n k) b x (Fin.castAdd a i) = x (Fin.castAdd a i) := by
    intro b x i
    apply setWire_of_ne
    intro heq
    have := congrArg Fin.val heq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hnat : ∀ b (x : Qubits (n + a)),
      (fun j : Fin a => t9_setWire (Fin.natAdd n k) b x (Fin.natAdd n j)) =
        t9_setWire k b (fun j : Fin a => x (Fin.natAdd n j)) := by
    intro b x
    funext j
    by_cases hjk : j = k
    · subst hjk; simp [setWire_self]
    · have hne : Fin.natAdd n j ≠ Fin.natAdd n k := fun h => hjk (Fin.natAdd_injective a n h)
      simp [setWire_of_ne hne, setWire_of_ne hjk]
  have hterm : ∀ b : Bool,
      ρ (p₁.1, fun i => t9_setWire (Fin.natAdd n k) b p₁.2 (Fin.castAdd a i))
          (p₂.1, fun i => t9_setWire (Fin.natAdd n k) b p₂.2 (Fin.castAdd a i)) *
        χ (fun j => t9_setWire (Fin.natAdd n k) b p₁.2 (Fin.natAdd n j)) *
        star (χ (fun j => t9_setWire (Fin.natAdd n k) b p₂.2 (Fin.natAdd n j))) =
      (ρ (p₁.1, fun i => p₁.2 (Fin.castAdd a i)) (p₂.1, fun i => p₂.2 (Fin.castAdd a i)) *
        rest (fun j => p₁.2 (Fin.natAdd n j)) *
        star (rest (fun j => p₂.2 (Fin.natAdd n j)))) *
        (v b * star (v b)) := by
    intro b
    simp_rw [hcast, hnat, hχ, setWire_self, hrest, star_mul']
    ring
  simp_rw [hterm, ← Finset.mul_sum, sum_bool_mul_star hv, mul_one]
  rw [hχ (fun j => p₁.2 (Fin.natAdd n j)), hχ (fun j => p₂.2 (Fin.natAdd n j))]
  simp only [star_mul']
  ring

private theorem hasPureWire_productAncVec_left_aux {n L M m_ref : ℕ} (α : Fin L → ℝ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) (i : Fin L) :
    t9_HasPureWire (Fin.natAdd n (Fin.castAdd M i)) (resourceVec (α i))
      (t9_tensorAncVec (t9_productAncVec α) ρ) := by
  let rest : Qubits (L + M) → ℂ := fun z =>
    (∏ i' ∈ Finset.univ.erase i, resourceVec (α i') (z (Fin.castAdd M i'))) *
      (∏ j : Fin M, basisVec false (z (Fin.natAdd L j)))
  refine hasPureWire_tensorAncVec_of_factor (Fin.castAdd M i) (resourceVec (α i))
    (norm_sq_resourceVec_aux (α i)) (t9_productAncVec α) rest ?_ ?_ ρ
  · intro z
    dsimp only [t9_productAncVec, rest]
    rw [← Finset.mul_prod_erase Finset.univ (fun i' => resourceVec (α i') (z (Fin.castAdd M i')))
      (Finset.mem_univ i)]
    ring
  · intro b z
    dsimp only [rest]
    congr 1
    · refine Finset.prod_congr rfl (fun i' hi' => ?_)
      have hne : Fin.castAdd M i' ≠ Fin.castAdd M i := by
        intro h
        apply (Finset.mem_erase.1 hi').1
        exact Fin.ext (by simpa using congrArg Fin.val h)
      rw [setWire_of_ne hne]
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      have hne : Fin.natAdd L j ≠ Fin.castAdd M i := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castAdd] at this
        omega
      rw [setWire_of_ne hne]

private theorem hasPureWire_productAncVec_right_aux {n L M m_ref : ℕ} (α : Fin L → ℝ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) (j : Fin M) :
    t9_HasPureWire (Fin.natAdd n (Fin.natAdd L j)) (basisVec false)
      (t9_tensorAncVec (t9_productAncVec α) ρ) := by
  let rest : Qubits (L + M) → ℂ := fun z =>
    (∏ i : Fin L, resourceVec (α i) (z (Fin.castAdd M i))) *
      (∏ j' ∈ Finset.univ.erase j, basisVec false (z (Fin.natAdd L j')))
  refine hasPureWire_tensorAncVec_of_factor (Fin.natAdd L j) (basisVec false)
    (norm_sq_basisVec_aux false) (t9_productAncVec α) rest ?_ ?_ ρ
  · intro z
    dsimp only [t9_productAncVec, rest]
    rw [← Finset.mul_prod_erase Finset.univ (fun j' => basisVec false (z (Fin.natAdd L j')))
      (Finset.mem_univ j)]
    ring
  · intro b z
    dsimp only [rest]
    congr 1
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      have hne : Fin.castAdd M i ≠ Fin.natAdd L j := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at this
        omega
      rw [setWire_of_ne hne]
    · refine Finset.prod_congr rfl (fun j' hj' => ?_)
      have hne : Fin.natAdd L j' ≠ Fin.natAdd L j := by
        intro h
        apply (Finset.mem_erase.1 hj').1
        exact Fin.natAdd_injective M L h
      rw [setWire_of_ne hne]

/-! ### Unitary conjugation and traceAndSetWire commutation -/

private theorem t9_unitConj_apply {N m_ref : ℕ}
    (U : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ)
    (r₁ r₂ : Fin m_ref) (y₁ y₂ : Qubits N) :
    t9_unitConj U σ (r₁, y₁) (r₂, y₂) =
      ∑ x₁ : Qubits N, ∑ x₂ : Qubits N,
        U y₁ x₁ * σ (r₁, x₁) (r₂, x₂) * star (U y₂ x₂) := by
  simp only [t9_unitConj, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type, star_mul']
  rw [Finset.sum_comm]
  have h1 : (∑ x₂ : Qubits N, ∑ r'' : Fin m_ref,
      (∑ r' : Fin m_ref, ∑ x₁ : Qubits N,
        (if r₁ = r' then 1 else 0) * U y₁ x₁ * σ (r', x₁) (r'', x₂)) *
        (star (if r₂ = r'' then (1 : ℂ) else 0) * star (U y₂ x₂))) =
      ∑ x₂ : Qubits N,
        (∑ x₁ : Qubits N, U y₁ x₁ * σ (r₁, x₁) (r₂, x₂)) * star (U y₂ x₂) := by
    refine Finset.sum_congr rfl (fun x₂ _ => ?_)
    rw [Fintype.sum_eq_single r₂ (fun r'' hr'' => by simp [hr''.symm])]
    simp only [↓reduceIte, star_one, one_mul]
    congr 1
    rw [Fintype.sum_eq_single r₁ (fun r' hr' => by simp [hr'.symm])]
    simp
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x₁ _ => ?_)
  rw [Finset.sum_mul]

private theorem t9_unitConj_mul {N m_ref : ℕ}
    (A B : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj A (t9_unitConj B σ) = t9_unitConj (A * B) σ := by
  simp only [t9_unitConj]
  have hk : ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (A * B)) =
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ A) *
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ B) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [hk, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem embedOp_swapBit_eq {k N : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin N) {q : Fin N}
    (hq : q ∉ Set.range w) (b : Bool) (y x : Qubits N) :
    embedOp M w y x = embedOp M w (t9_setWire q b y) (swapBit q (y q) b x) := by
  have hcomp_y : (t9_setWire q b y) ∘ w = y ∘ w := by
    funext i
    dsimp only [Function.comp_apply]
    exact setWire_of_ne (fun h => hq ⟨i, h⟩) b y
  by_cases hxy : x q = y q
  · have hswap : swapBit q (y q) b x = t9_setWire q b x := by
      simp [swapBit, hxy]
    have hcomp_x : (t9_setWire q b x) ∘ w = x ∘ w := by
      funext i
      dsimp only [Function.comp_apply]
      exact setWire_of_ne (fun h => hq ⟨i, h⟩) b x
    rw [hswap]
    simp only [embedOp, Matrix.of_apply, hcomp_y, hcomp_x]
    congr 1
    apply propext
    constructor
    · intro h a ha
      by_cases haq : a = q
      · subst haq; simp [setWire_self]
      · simp [setWire_of_ne haq, h a ha]
    · intro h a ha
      by_cases haq : a = q
      · subst haq; exact hxy.symm
      · have := h a ha
        simpa [setWire_of_ne haq] using this
  · have h1 : embedOp M w y x = 0 := by
      simp only [embedOp, Matrix.of_apply]
      rw [if_neg (fun h => hxy (h q hq).symm)]
    have h2 : embedOp M w (t9_setWire q b y) (swapBit q (y q) b x) = 0 := by
      simp only [embedOp, Matrix.of_apply]
      rw [if_neg]
      intro h
      have hq' := h q hq
      rw [setWire_self] at hq'
      have hx' : swapBit q (y q) b x q = b := hq'.symm
      rw [swapBit_apply_eq_iff] at hx'
      exact hxy hx'
    rw [h1, h2]

private theorem traceAndSetWire_unitConj_embedOp_aux {k N m_ref : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin N) {q : Fin N}
    (hq : q ∉ Set.range w) (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj (embedOp M w) (t9_traceAndSetWire q v σ) =
      t9_traceAndSetWire q v (t9_unitConj (embedOp M w) σ) := by
  ext p₁ p₂
  rcases p₁ with ⟨r₁, y₁⟩
  rcases p₂ with ⟨r₂, y₂⟩
  rw [t9_unitConj_apply]
  simp only [t9_traceAndSetWire, Matrix.of_apply, t9_unitConj_apply]
  have hleft : (∑ x₁ : Qubits N, ∑ x₂ : Qubits N,
      embedOp M w y₁ x₁ *
        ((∑ b : Bool, σ (r₁, t9_setWire q b x₁) (r₂, t9_setWire q b x₂)) *
          v (x₁ q) * star (v (x₂ q))) *
        star (embedOp M w y₂ x₂)) =
      (∑ b : Bool, ∑ x₁ : Qubits N, ∑ x₂ : Qubits N,
        embedOp M w y₁ x₁ * σ (r₁, t9_setWire q b x₁) (r₂, t9_setWire q b x₂) *
          star (embedOp M w y₂ x₂)) *
        v (y₁ q) * star (v (y₂ q)) := by
    have hterm : ∀ x₁ x₂ : Qubits N,
        embedOp M w y₁ x₁ *
          ((∑ b : Bool, σ (r₁, t9_setWire q b x₁) (r₂, t9_setWire q b x₂)) *
            v (x₁ q) * star (v (x₂ q))) *
          star (embedOp M w y₂ x₂) =
        ∑ b : Bool,
          (embedOp M w y₁ x₁ * σ (r₁, t9_setWire q b x₁) (r₂, t9_setWire q b x₂) *
            star (embedOp M w y₂ x₂)) *
            v (y₁ q) * star (v (y₂ q)) := by
      intro x₁ x₂
      by_cases hx₁ : x₁ q = y₁ q
      · by_cases hx₂ : x₂ q = y₂ q
        · rw [hx₁, hx₂]
          simp only [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun b _ => by ring)
        · have h0 : embedOp M w y₂ x₂ = 0 := by
            simp only [embedOp, Matrix.of_apply]
            exact if_neg (fun h => hx₂ (h q hq).symm)
          simp [h0]
      · have h0 : embedOp M w y₁ x₁ = 0 := by
          simp only [embedOp, Matrix.of_apply]
          exact if_neg (fun h => hx₁ (h q hq).symm)
        simp [h0]
    simp_rw [hterm]
    rw [Finset.sum_congr rfl (fun x₁ _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
  rw [hleft]
  congr 2
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have reindex : ∀ (f : Qubits N → Qubits N → ℂ),
      (∑ x₁ : Qubits N, ∑ x₂ : Qubits N, f x₁ x₂) =
        ∑ x₁ : Qubits N, ∑ x₂ : Qubits N, f (swapBit q (y₁ q) b x₁) (swapBit q (y₂ q) b x₂) := by
    intro f
    refine Fintype.sum_equiv
      ⟨swapBit q (y₁ q) b, swapBit q (y₁ q) b, swapBit_invol q (y₁ q) b, swapBit_invol q (y₁ q) b⟩
      _ _ (fun x₁ => ?_)
    refine Fintype.sum_equiv
      ⟨swapBit q (y₂ q) b, swapBit q (y₂ q) b, swapBit_invol q (y₂ q) b, swapBit_invol q (y₂ q) b⟩
      _ _ (fun x₂ => ?_)
    dsimp only [Equiv.coe_fn_mk]
    rw [swapBit_invol, swapBit_invol]
  rw [reindex (fun x₁ x₂ =>
    embedOp M w (t9_setWire q b y₁) x₁ * σ (r₁, x₁) (r₂, x₂) *
      star (embedOp M w (t9_setWire q b y₂) x₂))]
  refine Finset.sum_congr rfl (fun x₁ _ => Finset.sum_congr rfl (fun x₂ _ => ?_))
  rw [← embedOp_swapBit_eq M w hq b y₁ x₁, ← embedOp_swapBit_eq M w hq b y₂ x₂]
  by_cases hx₁ : x₁ q = y₁ q
  · by_cases hx₂ : x₂ q = y₂ q
    · have hs₁ : t9_setWire q b x₁ = swapBit q (y₁ q) b x₁ := by simp [swapBit, hx₁]
      have hs₂ : t9_setWire q b x₂ = swapBit q (y₂ q) b x₂ := by simp [swapBit, hx₂]
      rw [hs₁, hs₂]
    · have h0 : embedOp M w y₂ x₂ = 0 := by
        simp only [embedOp, Matrix.of_apply]
        exact if_neg (fun h => hx₂ (h q hq).symm)
      simp [h0]
  · have h0 : embedOp M w y₁ x₁ = 0 := by
      simp only [embedOp, Matrix.of_apply]
      exact if_neg (fun h => hx₁ (h q hq).symm)
    simp [h0]

private theorem proj_eq_embedOp {N : ℕ} (q : Fin N) (b : Bool) :
    AdaptiveCircuit.proj q b =
      embedOp (Matrix.diagonal fun a : Qubits 1 => if a 0 = b then 1 else 0)
        (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) := by
  ext y z
  simp only [AdaptiveCircuit.proj, embedOp, Matrix.diagonal_apply, Matrix.of_apply]
  have hw0 : (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) 0 = q := rfl
  by_cases hyz : y = z
  · subst hyz
    simp [hw0]
  · rw [if_neg hyz]
    by_cases h1 : ∀ a : Fin N, a ∉ Set.range
        (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) → y a = z a
    · rw [if_pos h1]
      by_cases h2 : y ∘ (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) =
          z ∘ (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N)
      · exfalso; apply hyz; funext a
        by_cases ha : a = q
        · subst ha; simpa [hw0] using congrFun h2 0
        · exact h1 a (by rintro ⟨i, hi⟩; exact ha hi.symm)
      · rw [if_neg h2]
    · rw [if_neg h1]

private theorem traceAndSetWire_unitConj_proj_aux {N m_ref : ℕ} {q' q : Fin N} (hq : q ≠ q')
    (b : Bool) (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj (AdaptiveCircuit.proj q' b) (t9_traceAndSetWire q v σ) =
      t9_traceAndSetWire q v (t9_unitConj (AdaptiveCircuit.proj q' b) σ) := by
  rw [proj_eq_embedOp]
  apply traceAndSetWire_unitConj_embedOp_aux
  rintro ⟨i, hi⟩
  exact hq hi.symm

private theorem partialTraceAnc_traceAndSetWire_aux {n a m_ref : ℕ} (u : Fin a) (v : Bool → ℂ)
    (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1)
    (σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (t9_traceAndSetWire (Fin.natAdd n u) v σ) = t9_partialTraceAnc σ := by
  ext p₁ p₂
  simp only [t9_partialTraceAnc, t9_traceAndSetWire, Matrix.of_apply]
  have happend_set : ∀ (p : Qubits n) (j : Qubits a) (b : Bool),
      t9_setWire (Fin.natAdd n u) b (Fin.append p j) = Fin.append p (t9_setWire u b j) := by
    intro p j b
    funext k
    rcases lt_or_ge k.val n with hlt | hge
    · let i : Fin n := ⟨k.val, hlt⟩
      have hk : k = Fin.castAdd a i := Fin.ext rfl
      have hne : k ≠ Fin.natAdd n u := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      rw [setWire_of_ne hne, hk, Fin.append_left, Fin.append_left]
    · have hk : k = Fin.natAdd n ⟨k.val - n, by omega⟩ := by
        ext; simp; omega
      rw [hk]
      by_cases hju : (⟨k.val - n, by omega⟩ : Fin a) = u
      · rw [hju, setWire_self, Fin.append_right, setWire_self]
      · have hne : Fin.natAdd n ⟨k.val - n, by omega⟩ ≠ Fin.natAdd n u :=
          fun h => hju (Fin.natAdd_injective a n h)
        rw [setWire_of_ne hne, Fin.append_right, Fin.append_right, setWire_of_ne hju]
  have happend_at : ∀ (p : Qubits n) (j : Qubits a),
      Fin.append p j (Fin.natAdd n u) = j u := fun p j => Fin.append_right p j u
  simp_rw [happend_set, happend_at]
  let G : Qubits a → ℂ := fun j => σ (p₁.1, Fin.append p₁.2 j) (p₂.1, Fin.append p₂.2 j)
  change (∑ j : Qubits a, (∑ b : Bool, G (t9_setWire u b j)) * v (j u) * star (v (j u))) =
    ∑ j : Qubits a, G j
  have hsplit : ∀ b : Bool,
      (∑ j : Qubits a, G (t9_setWire u b j) * (v (j u) * star (v (j u)))) =
        ∑ j' : Qubits a, if j' u = b then G j' else 0 := by
    intro b
    have hsplit_c : (∑ j : Qubits a, G (t9_setWire u b j) * (v (j u) * star (v (j u)))) =
        ∑ c : Bool, (v c * star (v c)) *
          (∑ j : Qubits a, if j u = c then G (t9_setWire u b j) else 0) := by
      have h1 : ∀ j : Qubits a,
          G (t9_setWire u b j) * (v (j u) * star (v (j u))) =
            ∑ c : Bool, (v c * star (v c)) * (if j u = c then G (t9_setWire u b j) else 0) := by
        intro j
        rw [Fintype.sum_bool]
        cases hj : j u <;> simp [mul_comm]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun c _ => by rw [Finset.mul_sum])
    rw [hsplit_c]
    have hconst : ∀ c : Bool,
        (∑ j : Qubits a, if j u = c then G (t9_setWire u b j) else 0) =
          ∑ j' : Qubits a, if j' u = b then G j' else 0 := by
      intro c
      rw [Fintype.sum_equiv
        ⟨swapBit u c b, swapBit u c b, swapBit_invol u c b, swapBit_invol u c b⟩
        _ (fun j' => if j' u = b then G j' else 0)]
      intro j
      dsimp only [Equiv.coe_fn_mk]
      by_cases hj : j u = c
      · have hj' : swapBit u c b j u = b := (swapBit_apply_eq_iff u c b j).2 hj
        have hset : t9_setWire u b j = swapBit u c b j := by simp [swapBit, hj]
        simp [hj, hj', hset]
      · have hj' : swapBit u c b j u ≠ b := fun h => hj ((swapBit_apply_eq_iff u c b j).1 h)
        simp [hj, hj']
    simp_rw [hconst, ← Finset.sum_mul, sum_bool_mul_star hv, one_mul]
  calc
    (∑ j : Qubits a, (∑ b : Bool, G (t9_setWire u b j)) * v (j u) * star (v (j u)))
      = ∑ b : Bool, ∑ j : Qubits a, G (t9_setWire u b j) * (v (j u) * star (v (j u))) := by
          simp_rw [mul_assoc, Finset.sum_mul]
          exact Finset.sum_comm
    _ = ∑ b : Bool, ∑ j' : Qubits a, if j' u = b then G j' else 0 := by
          refine Finset.sum_congr rfl (fun b _ => hsplit b)
    _ = ∑ j' : Qubits a, ∑ b : Bool, if j' u = b then G j' else 0 := Finset.sum_comm
    _ = ∑ j' : Qubits a, G j' := by
          refine Finset.sum_congr rfl (fun j' _ => by
            rw [Fintype.sum_bool]
            cases j' u <;> simp)

/-! ### `t9_rotOnWire` algebra -/

private theorem embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

private theorem embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

private theorem submatrix1_one :
    ((1 : Matrix Bool Bool ℂ).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) = 1 := by
  ext y z
  simp only [Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : y 0 = z 0
  · have hyz : y = z := by funext i; fin_cases i; exact h
    simp [hyz]
  · have hyz : y ≠ z := fun heq => h (congrFun heq 0)
    simp [h, hyz]

private theorem submatrix1_mul (A B : Matrix Bool Bool ℂ) :
    ((A * B).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) =
      (A.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) *
        (B.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) := by
  ext y z
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm]
  simp [Equiv.funUnique]

private theorem rot_zero : rot 0 = 1 := by
  ext a b
  cases a <;> cases b <;> simp [rot]

private theorem rot_two_pi_nat (k : ℕ) : rot (2 * Real.pi * (k : ℝ)) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [rot]
  rw [show 2 * (Real.pi : ℂ) * (k : ℂ) * Complex.I =
      (k : ℂ) * (2 * Real.pi * Complex.I) by ring]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

private theorem rot_add (α β : ℝ) : rot (α + β) = rot α * rot β := by
  ext a b
  cases a <;> cases b <;> simp [rot, Matrix.mul_apply]
  rw [add_mul, Complex.exp_add]

private theorem rotOnWire_zero_aux {N : ℕ} (q : Fin N) : t9_rotOnWire 0 q = 1 := by
  unfold t9_rotOnWire
  rw [rot_zero]
  change embedOp ((1 : Matrix Bool Bool ℂ).submatrix (fun b : Qubits 1 => b 0)
    (fun b : Qubits 1 => b 0)) _ = 1
  rw [submatrix1_one, embedOp_one]

private theorem rotOnWire_two_pi_nat_aux {N : ℕ} (k : ℕ) (q : Fin N) :
    t9_rotOnWire (2 * Real.pi * (k : ℝ)) q = 1 := by
  unfold t9_rotOnWire
  rw [rot_two_pi_nat]
  change embedOp ((1 : Matrix Bool Bool ℂ).submatrix (fun b : Qubits 1 => b 0)
    (fun b : Qubits 1 => b 0)) _ = 1
  rw [submatrix1_one, embedOp_one]

private theorem rotOnWire_add_aux {N : ℕ} (α β : ℝ) (q : Fin N) :
    t9_rotOnWire (α + β) q = t9_rotOnWire α q * t9_rotOnWire β q := by
  unfold t9_rotOnWire
  rw [rot_add]
  change embedOp (((rot α * rot β).submatrix (fun b : Qubits 1 => b 0)
      (fun b : Qubits 1 => b 0))) _ =
    embedOp ((rot α).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) _ *
      embedOp ((rot β).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) _
  rw [submatrix1_mul, embedOp_mul]

/-! ### State-injection step -/

private theorem hadamard_mem : Gate.ofMatrix1 hadamard ∈ CliffordT := by
  simp [CliffordT]

private theorem gateT_mem : Gate.ofMatrix1 gateT ∈ CliffordT := by
  simp [CliffordT]

private theorem cnot_mem : Gate.ofMatrix2 cnot ∈ CliffordT := by
  simp [CliffordT]

private theorem unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := rfl

private theorem unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (c : Circuit S n) :
    Circuit.unitary (g :: c) = Circuit.unitary c * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

private theorem unitary_append {S : Set Gate} {n : ℕ} (c₁ c₂ : Circuit S n) :
    Circuit.unitary (c₁ ++ c₂) = Circuit.unitary c₂ * Circuit.unitary c₁ := by
  simp [Circuit.unitary, List.map_append, List.reverse_append, List.prod_append]

private theorem unitary_replicate {S : Set Gate} {n : ℕ} (k : ℕ) (g : GateApp S n) :
    Circuit.unitary (List.replicate k g) = (embedOp g.gate.mat g.wires) ^ k := by
  induction k with
  | zero => simp [Circuit.unitary]
  | succ k ih =>
      rw [List.replicate_succ, unitary_cons, ih, pow_succ]

private noncomputable def resetFalseCirc : Circuit CliffordT 1 :=
  [app1 hadamard hadamard_mem 0]

private noncomputable def resetTrueCirc : Circuit CliffordT 1 :=
  [app1 hadamard hadamard_mem 0] ++ List.replicate 4 (app1 gateT gateT_mem 0)

private theorem resetFalseCirc_size : resetFalseCirc.size ≤ 1 := by
  simp [resetFalseCirc, Circuit.size]

private theorem resetTrueCirc_size : resetTrueCirc.size ≤ 5 := by
  simp [resetTrueCirc, Circuit.size]

private theorem gateT_pow_4 : gateT ^ 4 = pauliZ := by
  ext a b
  have hpow : (gateT ^ 4) a b = if a = b then (gateT a a) ^ 4 else 0 := by
    have h : gateT ^ 4 = Matrix.diagonal (fun x => (if x then Complex.exp (Complex.I * Real.pi / 4) else 1) ^ 4) := by
      dsimp [gateT]
      rw [Matrix.diagonal_pow]
      rfl
    rw [h, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp [gateT]
    · simp [hab]
  rw [hpow]
  cases a <;> cases b <;> simp [gateT, pauliZ]
  rw [← Complex.exp_nat_mul]
  have hpi : ((4 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = Real.pi * Complex.I := by
    push_cast; ring
  rw [hpi, Complex.exp_pi_mul_I]

private theorem embedOp_submatrix1 {n : ℕ} (M : Matrix Bool Bool ℂ)
    (w : Fin 1 ↪ Fin n) :
    embedOp (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) w =
      Matrix.of fun y z : Qubits n =>
        if ∀ a : Fin n, a ≠ w 0 → y a = z a then M (y (w 0)) (z (w 0)) else 0 := by
  ext y z
  have hr : ∀ a : Fin n, (a ∉ Set.range w) ↔ a ≠ w 0 := by
    intro a
    constructor
    · intro h heq; exact h ⟨0, heq.symm⟩
    · rintro h ⟨i, hi⟩; fin_cases i; exact h hi.symm
  simp only [embedOp, Matrix.submatrix_apply, Matrix.of_apply, Function.comp_apply]
  rw [if_congr (forall_congr' fun a => imp_congr_left (hr a)) rfl rfl]

private theorem gateApp1_unitary_eq (M : Matrix Bool Bool ℂ) (hm : Gate.ofMatrix1 M ∈ CliffordT) :
    embedOp (app1 M hm (0 : Fin 1)).gate.mat (app1 M hm (0 : Fin 1)).wires =
      M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0) := by
  change embedOp (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0))
    (⟨fun _ => (0 : Fin 1), fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 1) = _
  ext y z
  have hrange : ∀ a : Fin 1, a ∈ Set.range
      (⟨fun _ => (0 : Fin 1), fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 1) :=
    fun a => ⟨0, Fin.ext (by simp)⟩
  dsimp only [embedOp, Matrix.of_apply, Matrix.submatrix_apply]
  rw [if_pos (fun a ha => absurd (hrange a) ha)]
  rfl

private theorem resetFalseCirc_unitary_embed {N : ℕ} (q : Fin N) :
    embedOp resetFalseCirc.unitary (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) =
      Matrix.of fun y z : Qubits N =>
        if ∀ a : Fin N, a ≠ q → y a = z a then hadamard (y q) (z q) else 0 := by
  have hu : resetFalseCirc.unitary =
      hadamard.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0) := by
    rw [resetFalseCirc, unitary_cons, unitary_nil, one_mul]
    exact gateApp1_unitary_eq hadamard hadamard_mem
  rw [hu, embedOp_submatrix1]
  rfl

private theorem resetTrueCirc_unitary_embed {N : ℕ} (q : Fin N) :
    embedOp resetTrueCirc.unitary (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) =
      Matrix.of fun y z : Qubits N =>
        if ∀ a : Fin N, a ≠ q → y a = z a then (pauliZ * hadamard) (y q) (z q) else 0 := by
  have hu : resetTrueCirc.unitary =
      (pauliZ * hadamard).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0) := by
    rw [resetTrueCirc, unitary_append, unitary_replicate, unitary_cons, unitary_nil, one_mul]
    rw [gateApp1_unitary_eq gateT gateT_mem, gateApp1_unitary_eq hadamard hadamard_mem]
    have hpow : (gateT.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) ^ 4 =
        (gateT ^ 4).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0) := by
      rw [pow_succ, pow_succ, pow_succ, pow_one,
          pow_succ, pow_succ, pow_succ, pow_one,
          ← submatrix1_mul, ← submatrix1_mul, ← submatrix1_mul]
    rw [hpow, gateT_pow_4, ← submatrix1_mul]
  rw [hu, embedOp_submatrix1]
  rfl

private def cnotFun {n : ℕ} (a t : Fin n) (x : Qubits n) : Qubits n :=
  fun k => if k = t then xor (x t) (x a) else x k

private theorem cnotFun_invol {n : ℕ} (a t : Fin n) (hat : a ≠ t) (x : Qubits n) :
    cnotFun a t (cnotFun a t x) = x := by
  funext k
  by_cases hkt : k = t
  · subst hkt; simp [cnotFun, hat]
  · simp [cnotFun, hkt]

private theorem embedOp_cnotApp_apply {S : Set Gate} {n : ℕ} (h : Gate.ofMatrix2 cnot ∈ S)
    (a t : Fin n) (hat : a ≠ t) (z x : Qubits n) :
    embedOp (cnotApp h a t hat).gate.mat (cnotApp h a t hat).wires z x =
      if z = cnotFun a t x then 1 else 0 := by
  change (if ∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k
    then (if z a = x a ∧ z t = xor (x t) (x a) then (1 : ℂ) else 0) else 0) =
    if z = cnotFun a t x then 1 else 0
  have hc : (∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k) ∧
      (z a = x a ∧ z t = xor (x t) (x a)) ↔ z = cnotFun a t x := by
    constructor
    · rintro ⟨hk, ha, ht⟩
      funext k
      by_cases hkt : k = t
      · subst hkt; simp [cnotFun, ht]
      · by_cases hka : k = a
        · subst hka; simp [cnotFun, hat, ha]
        · have hnot : k ∉ Set.range ![a, t] := by
            rintro ⟨i, hi⟩
            fin_cases i
            · exact hka hi.symm
            · exact hkt hi.symm
          simp [cnotFun, hkt, hk k hnot]
    · intro hz
      subst hz
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hkt : k ≠ t := fun h => hk ⟨1, by simp [h]⟩
        simp [cnotFun, hkt]
      · simp [cnotFun, hat]
      · simp [cnotFun]
  by_cases h1 : ∀ k : Fin n, k ∉ Set.range ![a, t] → z k = x k
  · rw [if_pos h1]
    by_cases h2 : z a = x a ∧ z t = xor (x t) (x a)
    · rw [if_pos h2, if_pos (hc.1 ⟨h1, h2⟩)]
    · rw [if_neg h2, if_neg (fun h3 => h2 (hc.2 h3).2)]
  · rw [if_neg h1, if_neg (fun h3 => h1 (hc.2 h3).1)]

private theorem stateInjection_kraus_apply {N : ℕ} (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank)
    (b : Bool) (M : Matrix Bool Bool ℂ) (y x : Qubits N) :
    ((Matrix.of fun y z : Qubits N =>
        if ∀ a : Fin N, a ≠ w_bank → y a = z a then M (y w_bank) (z w_bank) else 0) *
      AdaptiveCircuit.proj w_bank b *
      embedOp (cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne).gate.mat
        (cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne).wires) y x =
      if x = t9_setWire w_bank (xor b (y w_targ)) y then M (y w_bank) b else 0 := by
  rw [Matrix.mul_apply]
  have h1 : ∀ z : Qubits N,
      ((Matrix.of fun y z : Qubits N =>
          if ∀ a : Fin N, a ≠ w_bank → y a = z a then M (y w_bank) (z w_bank) else 0) *
        AdaptiveCircuit.proj w_bank b) y z =
        if (∀ a : Fin N, a ≠ w_bank → y a = z a) ∧ z w_bank = b then M (y w_bank) b else 0 := by
    intro z
    rw [Matrix.mul_apply]
    simp only [AdaptiveCircuit.proj, Matrix.diagonal_apply, Matrix.of_apply]
    rw [Fintype.sum_eq_single z (fun z' hz' => by simp [hz'])]
    by_cases hzw : z w_bank = b
    · simp [hzw]
    · simp [hzw]
  simp_rw [h1, embedOp_cnotApp_apply]
  rw [Fintype.sum_eq_single (cnotFun w_targ w_bank x) (fun z hz => by simp [hz])]
  simp only [↓reduceIte, mul_one]
  have heq : ((∀ a : Fin N, a ≠ w_bank → y a = cnotFun w_targ w_bank x a) ∧
      cnotFun w_targ w_bank x w_bank = b) ↔
      x = t9_setWire w_bank (xor b (y w_targ)) y := by
    constructor
    · rintro ⟨ha, hb⟩
      funext a
      by_cases hab : a = w_bank
      · subst hab
        simp only [cnotFun, ↓reduceIte] at hb
        have hwt : y w_targ = x w_targ := by simpa [cnotFun, hne] using ha w_targ hne
        rw [setWire_self, ← hb, hwt]
        cases hx1 : x a <;> cases hx2 : x w_targ <;> simp
      · rw [setWire_of_ne hab]
        have := ha a hab
        simpa [cnotFun, hab] using this.symm
    · intro hx
      subst hx
      refine ⟨?_, ?_⟩
      · intro a ha
        simp [cnotFun, ha, setWire_of_ne ha]
      · simp only [cnotFun, ↓reduceIte, setWire_self, setWire_of_ne hne]
        cases b <;> cases y w_targ <;> decide
  by_cases hcond : (∀ a : Fin N, a ≠ w_bank → y a = cnotFun w_targ w_bank x a) ∧
      cnotFun w_targ w_bank x w_bank = b
  · rw [if_pos hcond, if_pos (heq.1 hcond)]
  · rw [if_neg hcond, if_neg (fun h => hcond (heq.2 h))]

private theorem hadamard_col_false (a : Bool) :
    hadamard a false = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  cases a <;> simp [hadamard]

private theorem pauliZ_hadamard_col_true (a : Bool) :
    (pauliZ * hadamard) a true = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  cases a <;> simp [pauliZ, hadamard, Matrix.mul_apply]

private theorem t9_rotOnWire_apply {N : ℕ} (θ : ℝ) (q : Fin N) (y x : Qubits N) :
    t9_rotOnWire θ q y x = if y = x then rot θ (y q) (y q) else 0 := by
  change embedOp ((rot θ).submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0))
    (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) y x = _
  rw [embedOp_submatrix1, Matrix.of_apply]
  have hq0 : (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) 0 = q := rfl
  rw [hq0]
  by_cases hyx : y = x
  · subst hyx; simp
  · rw [if_neg hyx]
    split_ifs with h1
    · have hq : y q ≠ x q := fun hq => by
        apply hyx; funext a
        by_cases ha : a = q
        · subst ha; exact hq
        · exact h1 a ha
      simp [rot, Matrix.diagonal_apply]
      intro h; exact absurd h hq
    · rfl

private theorem stateInjection_step_aux :
    ∃ (resetFalse resetTrue : Circuit CliffordT 1),
      resetFalse.size ≤ 1 ∧ resetTrue.size ≤ 5 ∧
      ∀ (N m_ref : ℕ) (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire w_bank (resourceVec θ) σ →
        let w1_bank : Fin 1 ↪ Fin N := ⟨fun _ => w_bank, fun i j _ => Subsingleton.elim i j⟩
        let g_cnot := cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne
        let σ_cnot := t9_unitConj (embedOp g_cnot.gate.mat g_cnot.wires) σ
        let P (b : Bool) := AdaptiveCircuit.proj w_bank b
        t9_unitConj (embedOp resetFalse.unitary w1_bank)
            (t9_unitConj (P false) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire θ w_targ)
              (t9_traceAndSetWire w_bank plusVec σ) ∧
        t9_unitConj (embedOp resetTrue.unitary w1_bank)
            (t9_unitConj (P true) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire (-θ) w_targ)
              (t9_traceAndSetWire w_bank plusVec σ) := by
  refine ⟨resetFalseCirc, resetTrueCirc, resetFalseCirc_size, resetTrueCirc_size, ?_⟩
  intro N m_ref w_targ w_bank hne θ σ h_pure
  dsimp only
  rw [t9_unitConj_mul, t9_unitConj_mul, t9_unitConj_mul, t9_unitConj_mul]
  rw [resetFalseCirc_unitary_embed, resetTrueCirc_unitary_embed]
  have h2_inv : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) := by
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hne0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
    field_simp [hne0]
    rw [hsq]
    norm_num
  constructor
  · ext ⟨r₁, y₁⟩ ⟨r₂, y₂⟩
    rw [t9_unitConj_apply, Matrix.smul_apply, smul_eq_mul, t9_unitConj_apply]
    simp_rw [stateInjection_kraus_apply w_targ w_bank hne false hadamard]
    rw [Fintype.sum_eq_single (t9_setWire w_bank (y₁ w_targ) y₁) (fun x₁ hx₁ => by simp [hx₁])]
    rw [Fintype.sum_eq_single (t9_setWire w_bank (y₂ w_targ) y₂) (fun x₂ hx₂ => by simp [hx₂])]
    simp only [Bool.false_xor, ↓reduceIte, hadamard_col_false]
    rw [Fintype.sum_eq_single y₁ (fun x₁ hx₁ => by simp [t9_rotOnWire_apply, hx₁.symm])]
    rw [Fintype.sum_eq_single y₂ (fun x₂ hx₂ => by simp [t9_rotOnWire_apply, hx₂.symm])]
    simp only [t9_rotOnWire_apply, ↓reduceIte, t9_traceAndSetWire, Matrix.of_apply]
    nth_rw 1 [← h_pure]
    simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_idem, setWire_self]
    have hrv : ∀ a : Bool,
        resourceVec θ a * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * rot θ a a * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
      intro a
      cases a <;> simp [resourceVec_false, resourceVec_true, rot]
      ring
    have hrv₁ := hrv (y₁ w_targ)
    have hrv₂ : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (resourceVec θ (y₂ w_targ)) =
        ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (rot θ (y₂ w_targ) (y₂ w_targ)) *
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
      have hs := congrArg star (hrv (y₂ w_targ))
      simp only [star_mul'] at hs
      have hstar_half : star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
        simp [Complex.conj_ofReal]
      rw [hstar_half] at hs
      rw [mul_comm ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ _, hs]
    have hstar_half : star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
      simp [Complex.conj_ofReal]
    simp only [plusVec]
    calc
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
          ((∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            resourceVec θ (y₁ w_targ) * star (resourceVec θ (y₂ w_targ))) *
          star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        = (∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            (resourceVec θ (y₁ w_targ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (resourceVec θ (y₂ w_targ))) := by
              rw [hstar_half]; ring
      _ = (∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * rot θ (y₁ w_targ) (y₁ w_targ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (rot θ (y₂ w_targ) (y₂ w_targ)) *
              ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
              rw [hrv₁, hrv₂]
      _ = ((1 / 2 : ℝ) : ℂ) *
            (rot θ (y₁ w_targ) (y₁ w_targ) *
              ((∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
                ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
              star (rot θ (y₂ w_targ) (y₂ w_targ))) := by
              rw [← h2_inv, hstar_half]; ring
  · ext ⟨r₁, y₁⟩ ⟨r₂, y₂⟩
    rw [t9_unitConj_apply, Matrix.smul_apply, smul_eq_mul, t9_unitConj_apply]
    simp_rw [stateInjection_kraus_apply w_targ w_bank hne true (pauliZ * hadamard)]
    rw [Fintype.sum_eq_single (t9_setWire w_bank (xor true (y₁ w_targ)) y₁)
      (fun x₁ hx₁ => by simp only [Bool.true_xor] at hx₁ ⊢; simp [hx₁])]
    rw [Fintype.sum_eq_single (t9_setWire w_bank (xor true (y₂ w_targ)) y₂)
      (fun x₂ hx₂ => by simp only [Bool.true_xor] at hx₂ ⊢; simp [hx₂])]
    simp only [↓reduceIte, pauliZ_hadamard_col_true]
    rw [Fintype.sum_eq_single y₁ (fun x₁ hx₁ => by simp [t9_rotOnWire_apply, hx₁.symm])]
    rw [Fintype.sum_eq_single y₂ (fun x₂ hx₂ => by simp [t9_rotOnWire_apply, hx₂.symm])]
    simp only [t9_rotOnWire_apply, ↓reduceIte, t9_traceAndSetWire, Matrix.of_apply]
    nth_rw 1 [← h_pure]
    simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_idem, setWire_self]
    have hrv : ∀ a : Bool,
        resourceVec θ (xor true a) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ =
          Complex.exp ((θ : ℂ) * Complex.I) *
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * rot (-θ) a a * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
      intro a
      cases a <;> simp [resourceVec_false, resourceVec_true, rot]
      · ring
      · rw [Complex.exp_neg]
        have hne_exp : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
        field_simp [hne_exp]
    have hrv₁ := hrv (y₁ w_targ)
    have hrv₂ := congrArg star (hrv (y₂ w_targ))
    have hstar_half : star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
      simp [Complex.conj_ofReal]
    have hexp_star : Complex.exp ((θ : ℂ) * Complex.I) *
        star (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
      change Complex.exp ((θ : ℂ) * Complex.I) * starRingEnd ℂ (Complex.exp ((θ : ℂ) * Complex.I)) = 1
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      norm_num
    simp only [plusVec]
    calc
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
          ((∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            resourceVec θ (xor true (y₁ w_targ)) * star (resourceVec θ (xor true (y₂ w_targ)))) *
          star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        = (∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            (resourceVec θ (xor true (y₁ w_targ)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            star (resourceVec θ (xor true (y₂ w_targ)) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
              simp only [star_mul', hstar_half]; ring
      _ = (Complex.exp ((θ : ℂ) * Complex.I) * star (Complex.exp ((θ : ℂ) * Complex.I))) *
            (∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
            (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * rot (-θ) (y₁ w_targ) (y₁ w_targ) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
            star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * rot (-θ) (y₂ w_targ) (y₂ w_targ) *
              ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
              rw [hrv₁, hrv₂]
              simp only [star_mul']
              ring
      _ = ((1 / 2 : ℝ) : ℂ) *
            (rot (-θ) (y₁ w_targ) (y₁ w_targ) *
              ((∑ b : Bool, σ (r₁, t9_setWire w_bank b y₁) (r₂, t9_setWire w_bank b y₂)) *
                ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) *
              star (rot (-θ) (y₂ w_targ) (y₂ w_targ))) := by
              rw [hexp_star, one_mul, ← h2_inv]
              simp only [star_mul', hstar_half]
              ring

/-! ### Phase-halving split: Toffoli synthesis and splitting `phaseHalving` -/

private noncomputable def hGate3 (q : Fin 3) : GateApp CliffordT 3 :=
  app1 hadamard hadamard_mem q

private noncomputable def tGate3 (q : Fin 3) : GateApp CliffordT 3 :=
  app1 gateT gateT_mem q

private def cnotGate3 (a t : Fin 3) (hat : a ≠ t) : GateApp CliffordT 3 :=
  cnotApp cnot_mem a t hat

private noncomputable def midCircuit : Circuit CliffordT 3 :=
  [tGate3 0, tGate3 1, tGate3 2, cnotGate3 0 1 (by decide)] ++
    List.replicate 7 (tGate3 1) ++
    [cnotGate3 2 1 (by decide), tGate3 1, cnotGate3 0 2 (by decide)] ++
    List.replicate 7 (tGate3 2) ++
    [cnotGate3 0 1 (by decide)] ++
    List.replicate 7 (tGate3 1) ++
    [cnotGate3 0 2 (by decide), cnotGate3 2 1 (by decide)]

private noncomputable def toffoliCircuit : Circuit CliffordT 3 :=
  [hGate3 2] ++ midCircuit ++ [hGate3 2]

private theorem toffoliCircuit_size : toffoliCircuit.size = 33 := by
  simp [toffoliCircuit, midCircuit, Circuit.size]

private noncomputable def ω : ℂ := Complex.exp (Complex.I * Real.pi / 4)

private theorem ω_pow_4 : ω ^ 4 = -1 := by
  dsimp [ω]
  rw [← Complex.exp_nat_mul]
  have h : ((4 : ℕ) : ℂ) * (Complex.I * Real.pi / 4) = Real.pi * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_pi_mul_I]

private theorem ω_pow_8 : ω ^ 8 = 1 := by
  calc
    ω ^ 8 = (ω ^ 4) ^ 2 := by ring
    _ = (-1) ^ 2 := by rw [ω_pow_4]
    _ = 1 := by norm_num

private theorem ω_pow_mod_8 (k : ℕ) : ω ^ k = ω ^ (k % 8) := by
  have h := Nat.div_add_mod k 8
  conv_lhs => rw [← h, pow_add, pow_mul, ω_pow_8, one_pow, one_mul]

private theorem embedOp_app1 {S : Set Gate} {n : ℕ} (M : Matrix Bool Bool ℂ)
    (h : Gate.ofMatrix1 M ∈ S) (q : Fin n) :
    embedOp (app1 M h q).gate.mat (app1 M h q).wires =
      Matrix.of fun y z => if ∀ a : Fin n, a ≠ q → y a = z a then M (y q) (z q) else 0 := by
  ext y z
  change (if ∀ a : Fin n, a ∉ Set.range (fun _ : Fin 1 => q) → y a = z a
    then M (y q) (z q) else 0) = _
  have hr : ∀ a : Fin n, (a ∉ Set.range (fun _ : Fin 1 => q)) ↔ a ≠ q := by
    intro a; simp
  simp only [hr, Matrix.of_apply]

private theorem embedOp_tGate {n : ℕ} (q : Fin n) (h : Gate.ofMatrix1 gateT ∈ CliffordT) :
    embedOp (app1 gateT h q).gate.mat (app1 gateT h q).wires =
      Matrix.diagonal (fun x : Qubits n => ω ^ (if x q then 1 else 0)) := by
  rw [embedOp_app1]
  ext y z
  simp only [Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hyz : y = z
  · subst hyz
    simp only [ne_eq, implies_true, ↓reduceIte, gateT, Matrix.diagonal_apply]
    cases y q <;> simp [ω]
  · rw [if_neg hyz]
    split_ifs with h1
    · simp only [gateT, Matrix.diagonal_apply]
      have hq : y q ≠ z q := by
        intro hq
        apply hyz
        funext a
        by_cases ha : a = q
        · subst ha; exact hq
        · exact h1 a ha
      exact if_neg hq
    · rfl

private theorem diag_ω_pow {n : ℕ} (f : Qubits n → ℕ) (k : ℕ) :
    (Matrix.diagonal (fun x => ω ^ f x)) ^ k = Matrix.diagonal (fun x => ω ^ (k * f x)) := by
  rw [Matrix.diagonal_pow]
  congr 1
  funext x
  simp only [Pi.pow_apply, ← pow_mul, mul_comm]

private def permMatrix {α : Type*} [DecidableEq α] (f : α → α) : Matrix α α ℂ :=
  Matrix.of fun y z => if y = f z then 1 else 0

private theorem permMatrix_id {α : Type*} [DecidableEq α] :
    permMatrix (id : α → α) = 1 := by
  ext y z
  simp [permMatrix, Matrix.one_apply]

private theorem permMatrix_mul_permMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → α) :
    permMatrix f * permMatrix g = permMatrix (f ∘ g) := by
  ext y z
  simp [permMatrix, Matrix.mul_apply]

private theorem permMatrix_cnot_mul_diag_mul {n : ℕ} (a t : Fin n) (hat : a ≠ t)
    (d : Qubits n → ℂ) (X : Matrix (Qubits n) (Qubits n) ℂ) :
    permMatrix (cnotFun a t) * (Matrix.diagonal d * X) =
      Matrix.diagonal (fun x => d (cnotFun a t x)) * (permMatrix (cnotFun a t) * X) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  congr 1
  ext y z
  simp only [permMatrix, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply,
    mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hyz : y = cnotFun a t z <;> simp [hyz, cnotFun_invol a t hat z]

private theorem diag_mul_diag_mul {α : Type*} [Fintype α] [DecidableEq α]
    (d₁ d₂ : α → ℂ) (X : Matrix α α ℂ) :
    Matrix.diagonal d₁ * (Matrix.diagonal d₂ * X) =
      Matrix.diagonal (fun x => d₁ x * d₂ x) * X := by
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

private theorem embedOp_cnotApp {S : Set Gate} {n : ℕ} (h : Gate.ofMatrix2 cnot ∈ S)
    (a t : Fin n) (hat : a ≠ t) :
    embedOp (cnotApp h a t hat).gate.mat (cnotApp h a t hat).wires = permMatrix (cnotFun a t) := by
  ext y z
  rw [embedOp_cnotApp_apply h a t hat]
  rfl

private theorem midCircuit_unitary :
    midCircuit.unitary =
      Matrix.diagonal (fun x : Qubits 3 => if x 0 && x 1 && x 2 then (-1 : ℂ) else 1) := by
  have hunit : midCircuit.unitary = midCircuit.unitary * permMatrix id := by
    rw [permMatrix_id, Matrix.mul_one]
  rw [hunit, midCircuit]
  simp only [unitary_append, unitary_cons, unitary_nil, unitary_replicate, one_mul]
  simp only [tGate3, cnotGate3, embedOp_tGate, diag_ω_pow, embedOp_cnotApp]
  simp only [Matrix.mul_assoc,
    permMatrix_cnot_mul_diag_mul (0 : Fin 3) 1 (by decide),
    permMatrix_cnot_mul_diag_mul (2 : Fin 3) 1 (by decide),
    permMatrix_cnot_mul_diag_mul (0 : Fin 3) 2 (by decide),
    diag_mul_diag_mul]
  simp only [permMatrix_mul_permMatrix]
  have hid : (cnotFun (2 : Fin 3) 1 ∘ cnotFun 0 2 ∘ cnotFun 0 1 ∘ cnotFun 0 2 ∘ cnotFun 2 1 ∘
      cnotFun 0 1 ∘ id : Qubits 3 → Qubits 3) = id := by
    funext x k
    fin_cases k <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp [cnotFun, h0, h1, h2]
  rw [hid, permMatrix_id, Matrix.mul_one]
  congr 1
  funext x
  simp only [← pow_add]
  rw [ω_pow_mod_8,
    show (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) =
      ω ^ (if x 0 && x 1 && x 2 then 4 else 0) by
        by_cases h0 : x 0 && x 1 && x 2 <;> simp [h0, ω_pow_4]]
  congr 1
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [cnotFun, h0, h1, h2]

private theorem hadamard_pauliZ_hadamard : hadamard * pauliZ * hadamard = pauliX := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  ext a b
  cases a <;> cases b <;>
    simp [hadamard, pauliZ, pauliX, Matrix.mul_apply] <;>
    ring_nf <;> field_simp <;> simp [h2]

private theorem hGate3_2_apply (y x : Qubits 3) :
    embedOp (hGate3 2).gate.mat (hGate3 2).wires y x =
      if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0 := by
  rw [hGate3, embedOp_app1, Matrix.of_apply]
  have hr : (∀ a : Fin 3, a ≠ 2 → y a = x a) ↔ (y 0 = x 0 ∧ y 1 = x 1) := by
    constructor
    · intro h; exact ⟨h 0 (by decide), h 1 (by decide)⟩
    · intro ⟨h0, h1⟩ a ha
      fin_cases a
      · exact h0
      · exact h1
      · exact absurd rfl ha
  simp only [hr]

private theorem mul_diag_mul_apply {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Matrix α α ℂ) (d : α → ℂ) (y z : α) :
    (A * Matrix.diagonal d * B) y z = ∑ x : α, A y x * d x * B x z := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

private def qubits3Equiv : Qubits 3 ≃ Bool × Bool × Bool where
  toFun x := (x 0, x 1, x 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

private theorem sum_qubits3 (f : Qubits 3 → ℂ) :
    (∑ x : Qubits 3, f x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, f ![a, b, c] := by
  rw [← Equiv.sum_comp qubits3Equiv.symm]
  simp_rw [Fintype.sum_prod_type]
  rfl

private theorem toffoliCircuit_unitary : toffoliCircuit.unitary = toffoliMat := by
  rw [toffoliCircuit, unitary_append, unitary_append, unitary_cons, unitary_nil, one_mul]
  rw [midCircuit_unitary]
  ext y z
  rw [← Matrix.mul_assoc, mul_diag_mul_apply]
  simp only [hGate3_2_apply]
  by_cases hyz : y 0 = z 0 ∧ y 1 = z 1
  · have hsum : (∑ x : Qubits 3,
        (if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0) *
          (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) *
          (if x 0 = z 0 ∧ x 1 = z 1 then hadamard (x 2) (z 2) else 0)) =
        ∑ c : Bool, hadamard (y 2) c * (if z 0 && z 1 && c then (-1 : ℂ) else 1) *
          hadamard c (z 2) := by
      rw [sum_qubits3]
      rw [Fintype.sum_eq_single (z 0) (fun a ha => by simp [hyz.1, ha.symm])]
      rw [Fintype.sum_eq_single (z 1) (fun b hb => by simp [hyz.2, hb.symm])]
      simp [hyz.1, hyz.2]
    rw [hsum]
    by_cases h01 : z 0 = true ∧ z 1 = true
    · simp only [h01.1, h01.2, Bool.true_and]
      have hzh : ∑ c : Bool, hadamard (y 2) c * (if c = true then (-1 : ℂ) else 1) *
          hadamard c (z 2) = (hadamard * pauliZ * hadamard) (y 2) (z 2) := by
        simp [Matrix.mul_apply, pauliZ]
      rw [hzh, hadamard_pauliZ_hadamard]
      cases hy2 : y 2 <;> cases hz2 : z 2 <;>
        simp [pauliX, toffoliMat, hyz.1, hyz.2, h01.1, h01.2, hy2, hz2]
    · have hfalse : (z 0 && z 1) = false := by
        cases h0 : z 0 <;> cases h1 : z 1 <;> simp_all
      simp only [hfalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, mul_one]
      have hh : ∑ c : Bool, hadamard (y 2) c * hadamard c (z 2) =
          (hadamard * hadamard) (y 2) (z 2) := rfl
      rw [hh, hadamard_mul_self, Matrix.one_apply]
      simp [toffoliMat, hyz.1, hyz.2, hfalse]
  · have hzero : (∑ x : Qubits 3,
        (if y 0 = x 0 ∧ y 1 = x 1 then hadamard (y 2) (x 2) else 0) *
          (if (x 0 && x 1 && x 2) = true then (-1 : ℂ) else 1) *
          (if x 0 = z 0 ∧ x 1 = z 1 then hadamard (x 2) (z 2) else 0)) = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases h1 : y 0 = x 0 ∧ y 1 = x 1
      · have h2 : ¬ (x 0 = z 0 ∧ x 1 = z 1) := fun h2 =>
          hyz ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
        rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul, zero_mul]
    rw [hzero]
    simp only [toffoliMat, Matrix.of_apply]
    rw [if_neg (fun h => hyz ⟨h.1, h.2.1⟩)]

private def liftToffoliGateCT (g : GateApp CliffordT 3) : GateApp CliffordT 4 :=
  ⟨g.gate, g.mem, g.wires.trans toffoliWires⟩

private def cT4_cliffordT (cT : Circuit CliffordT 3) : Circuit CliffordT 4 :=
  cT.map liftToffoliGateCT

private theorem cT4_cliffordT_unitary (cT : Circuit CliffordT 3) :
    (cT4_cliffordT cT).unitary = embedOp cT.unitary toffoliWires := by
  induction cT with
  | nil =>
      simp [cT4_cliffordT, unitary_nil, embedOp_one]
  | cons g cs ih =>
      dsimp only [cT4_cliffordT]
      rw [List.map_cons, unitary_cons]
      change (cT4_cliffordT cs).unitary *
          embedOp (liftToffoliGateCT g).gate.mat (liftToffoliGateCT g).wires = _
      rw [ih]
      have hgate : embedOp (liftToffoliGateCT g).gate.mat (liftToffoliGateCT g).wires =
          embedOp (embedOp g.gate.mat g.wires) toffoliWires := by
        simpa [liftToffoliGateCT] using (embedOp_trans g.gate.mat g.wires toffoliWires).symm
      rw [hgate, ← embedOp_mul, unitary_cons]

private noncomputable def half1Circ : Circuit CliffordT 4 :=
  [cnotApp cnot_mem 1 0 (by decide),
   cnotApp cnot_mem 2 0 (by decide),
   cnotApp cnot_mem 0 1 (by decide),
   cnotApp cnot_mem 0 2 (by decide)] ++
  cT4_cliffordT toffoliCircuit ++
  [cnotApp cnot_mem 0 3 (by decide)]

private noncomputable def half2Circ : Circuit CliffordT 4 :=
  [cnotApp cnot_mem 0 3 (by decide)] ++
  cT4_cliffordT toffoliCircuit ++
  [cnotApp cnot_mem 0 2 (by decide),
   cnotApp cnot_mem 0 1 (by decide)]

private theorem half1Circ_size : half1Circ.size ≤ 38 := by
  simp only [half1Circ, Circuit.size, List.length_append, List.length_cons,
    List.length_nil, cT4_cliffordT, List.length_map]
  have hlen : toffoliCircuit.length = 33 := toffoliCircuit_size
  omega

private theorem half2Circ_size : half2Circ.size ≤ 36 := by
  simp only [half2Circ, Circuit.size, List.length_append, List.length_cons,
    List.length_nil, cT4_cliffordT, List.length_map]
  have hlen : toffoliCircuit.length = 33 := toffoliCircuit_size
  omega

private theorem phaseHalving_split_unitary {N : ℕ} (w : Fin 4 ↪ Fin N) (θ : ℝ) :
    embedOp half2Circ.unitary w * t9_rotOnWire (2 * θ) (w 3) * embedOp half1Circ.unitary w =
      embedOp (phaseHalving θ).unitary w := by
  have hw3 : (⟨fun _ => w 3, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) =
      (⟨fun _ => (3 : Fin 4), fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 4).trans w := by
    ext i; rfl
  have hrot : t9_rotOnWire (2 * θ) (w 3) =
      embedOp (embedOp (Gate.ofMatrix1 (rot (2 * θ))).mat
        (⟨fun _ => (3 : Fin 4), fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 4)) w := by
    unfold t9_rotOnWire
    change embedOp ((rot (2 * θ)).submatrix (fun b : Qubits 1 => b 0)
        (fun b : Qubits 1 => b 0))
      (⟨fun _ => w 3, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin N) = _
    rw [hw3]
    exact (embedOp_trans ((rot (2 * θ)).submatrix (fun b : Qubits 1 => b 0)
      (fun b : Qubits 1 => b 0))
      (⟨fun _ => (3 : Fin 4), fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin 4) w).symm
  rw [hrot, ← embedOp_mul, ← embedOp_mul]
  congr 1
  dsimp only [half1Circ, half2Circ, phaseHalving]
  simp only [unitary_append, unitary_cons, unitary_nil, one_mul, cT4_cliffordT_unitary,
    toffoliCircuit_unitary]
  simp only [Matrix.mul_assoc]
  rfl

private noncomputable def patchWires {k N : ℕ} (w : Fin k ↪ Fin N) (y : Qubits N) (z : Qubits k) :
    Qubits N :=
  fun a => if h : ∃ i : Fin k, w i = a then z (Classical.choose h) else y a

private theorem patchWires_apply_w {k N : ℕ} (w : Fin k ↪ Fin N) (y : Qubits N) (z : Qubits k)
    (i : Fin k) : patchWires w y z (w i) = z i := by
  have h : ∃ i' : Fin k, w i' = w i := ⟨i, rfl⟩
  simp only [patchWires, h, ↓reduceDIte]
  exact congrArg z (w.injective (Classical.choose_spec h))

private theorem patchWires_apply_not_mem {k N : ℕ} (w : Fin k ↪ Fin N) (y : Qubits N)
    (z : Qubits k) {a : Fin N} (ha : a ∉ Set.range w) :
    patchWires w y z a = y a := by
  have hnot : ¬ ∃ i : Fin k, w i = a := fun ⟨i, hi⟩ => ha ⟨i, hi⟩
  simp [patchWires, hnot]

private theorem setWire_patchWires {k N : ℕ} (w : Fin k ↪ Fin N) (y : Qubits N)
    (z : Qubits k) (i : Fin k) (b : Bool) :
    t9_setWire (w i) b (patchWires w y z) = patchWires w y (t9_setWire i b z) := by
  funext a
  by_cases ha : a ∈ Set.range w
  · rcases ha with ⟨j, rfl⟩
    by_cases hij : j = i
    · subst hij; simp [setWire_self, patchWires_apply_w]
    · have hne : w j ≠ w i := fun h => hij (w.injective h)
      simp [setWire_of_ne hne, patchWires_apply_w, setWire_of_ne hij]
  · have hne : a ≠ w i := fun h => ha ⟨i, h.symm⟩
    simp [setWire_of_ne hne, patchWires_apply_not_mem w y _ ha]

private theorem setWire_patchWires_eq_self {k N : ℕ} (w : Fin k ↪ Fin N) (y : Qubits N)
    (z : Qubits k) (i : Fin k) (b : Bool) :
    patchWires w (t9_setWire (w i) b y) z = patchWires w y z := by
  funext a
  by_cases ha : a ∈ Set.range w
  · rcases ha with ⟨j, rfl⟩
    simp [patchWires_apply_w]
  · have hne : a ≠ w i := fun h => ha ⟨i, h.symm⟩
    simp [patchWires_apply_not_mem w _ z ha, setWire_of_ne hne]

private theorem sum_embedOp_mul {k N : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (w : Fin k ↪ Fin N) (y : Qubits N) (f : Qubits N → ℂ) :
    (∑ x : Qubits N, embedOp M w y x * f x) =
      ∑ z : Qubits k, M (y ∘ w) z * f (patchWires w y z) := by
  have hfilt : (∑ x : Qubits N, embedOp M w y x * f x) =
      ∑ x ∈ Finset.univ.filter (fun x : Qubits N => ∀ a : Fin N, a ∉ Set.range w → y a = x a),
        M (y ∘ w) (x ∘ w) * f x := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : Qubits N => ∀ a : Fin N, a ∉ Set.range w → y a = x a)]
    have hzero : (∑ x ∈ Finset.univ.filter (fun x : Qubits N => ¬ ∀ a : Fin N, a ∉ Set.range w → y a = x a),
        embedOp M w y x * f x) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      dsimp only [embedOp, Matrix.of_apply]
      rw [if_neg hx, zero_mul]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    dsimp only [embedOp, Matrix.of_apply]
    rw [if_pos hx]
  rw [hfilt]
  refine Finset.sum_bij (fun x _ => x ∘ w)
    (fun _ _ => Finset.mem_univ _)
    (fun x₁ hx₁ x₂ hx₂ h => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
      funext a
      by_cases ha : a ∈ Set.range w
      · rcases ha with ⟨i, rfl⟩; exact congrFun h i
      · exact (hx₁ a ha).symm.trans (hx₂ a ha))
    (fun z _ => by
      refine ⟨patchWires w y z, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro a ha
        exact (patchWires_apply_not_mem w y z ha).symm
      · funext i
        exact patchWires_apply_w w y z i)
    (fun x hx => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hpx : patchWires w y (x ∘ w) = x := by
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨i, rfl⟩; exact patchWires_apply_w w y (x ∘ w) i
        · rw [patchWires_apply_not_mem w y _ ha, hx a ha]
      rw [hpx])

private theorem vec4_rot_basisVec_apply (θ : ℝ) (b₁ c : Bool) :
    (rot θ).mulVec (basisVec b₁) c = rot θ c c * basisVec b₁ c := by
  cases b₁ <;> cases c <;> simp [rot, basisVec, Matrix.mulVec, dotProduct]

private theorem sum_factor_2 {ι₁ ι₂ κ₁ κ₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] [Fintype κ₁] [Fintype κ₂]
    (S : κ₁ → κ₂ → ℂ) (A : ι₁ → κ₁ → ℂ) (B : ι₂ → κ₂ → ℂ) :
    (∑ x : ι₁, ∑ y : ι₂, ∑ k₁ : κ₁, ∑ k₂ : κ₂, S k₁ k₂ * A x k₁ * star (B y k₂)) =
      ∑ k₁ : κ₁, ∑ k₂ : κ₂, S k₁ k₂ * (∑ x : ι₁, A x k₁) * star (∑ y : ι₂, B y k₂) := by
  symm
  calc
    (∑ k₁ : κ₁, ∑ k₂ : κ₂, S k₁ k₂ * (∑ x : ι₁, A x k₁) * star (∑ y : ι₂, B y k₂))
      = ∑ k₁ : κ₁, ∑ k₂ : κ₂, ∑ x : ι₁, ∑ y : ι₂, S k₁ k₂ * A x k₁ * star (B y k₂) := by
          refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
          rw [star_sum, Finset.mul_sum]
          have hswap : (∑ i : ι₂, (S k₁ k₂ * ∑ x : ι₁, A x k₁) * star (B i k₂)) =
              ∑ i : ι₂, ∑ x : ι₁, S k₁ k₂ * A x k₁ * star (B i k₂) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum, Finset.sum_mul]
          rw [hswap, Finset.sum_comm]
    _ = ∑ k₁ : κ₁, ∑ x : ι₁, ∑ k₂ : κ₂, ∑ y : ι₂, S k₁ k₂ * A x k₁ * star (B y k₂) := by
          refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_comm)
    _ = ∑ x : ι₁, ∑ k₁ : κ₁, ∑ k₂ : κ₂, ∑ y : ι₂, S k₁ k₂ * A x k₁ * star (B y k₂) :=
          Finset.sum_comm
    _ = ∑ x : ι₁, ∑ k₁ : κ₁, ∑ y : ι₂, ∑ k₂ : κ₂, S k₁ k₂ * A x k₁ * star (B y k₂) := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun k₁ _ => Finset.sum_comm))
    _ = ∑ x : ι₁, ∑ y : ι₂, ∑ k₁ : κ₁, ∑ k₂ : κ₂, S k₁ k₂ * A x k₁ * star (B y k₂) := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

private theorem phaseHalving_split_aux :
    ∃ (half1 half2 : Circuit CliffordT 4),
      half1.size ≤ 38 ∧ half2.size ≤ 36 ∧
      ∀ (N m_ref : ℕ) (w : Fin 4 ↪ Fin N) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire (w 0) (resourceVec θ) σ →
        t9_HasPureWire (w 2) plusVec σ →
        t9_HasPureWire (w 3) (basisVec false) σ →
        t9_unitConj (embedOp half2.unitary w)
          (t9_unitConj (t9_rotOnWire (2 * θ) (w 3))
            (t9_unitConj (embedOp half1.unitary w) σ)) =
          t9_unitConj (t9_rotOnWire θ (w 1))
            (t9_traceAndSetWire (w 2) (resourceVec θ) σ) := by
  refine ⟨half1Circ, half2Circ, half1Circ_size, half2Circ_size, ?_⟩
  intro N m_ref w θ σ h0 h2 h3
  rw [t9_unitConj_mul, t9_unitConj_mul, phaseHalving_split_unitary]
  ext ⟨r₁, y₁⟩ ⟨r₂, y₂⟩
  rw [t9_unitConj_apply, t9_unitConj_apply]
  let U := (phaseHalving θ).unitary
  have hlhs_z : (∑ x₁ : Qubits N, ∑ x₂ : Qubits N,
      embedOp U w y₁ x₁ * σ (r₁, x₁) (r₂, x₂) * star (embedOp U w y₂ x₂)) =
      ∑ z₁ : Qubits 4, ∑ z₂ : Qubits 4,
        U (y₁ ∘ w) z₁ * σ (r₁, patchWires w y₁ z₁) (r₂, patchWires w y₂ z₂) *
          star (U (y₂ ∘ w) z₂) := by
    have hinner : ∀ x₁ : Qubits N,
        (∑ x₂ : Qubits N, embedOp U w y₁ x₁ * σ (r₁, x₁) (r₂, x₂) * star (embedOp U w y₂ x₂)) =
        embedOp U w y₁ x₁ *
          star (∑ x₂ : Qubits N, embedOp U w y₂ x₂ * star (σ (r₁, x₁) (r₂, x₂))) := by
      intro x₁
      simp only [star_sum, star_mul', star_star, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₂ _ => by ring)
    simp_rw [hinner, sum_embedOp_mul]
    refine Finset.sum_congr rfl (fun z₁ _ => ?_)
    simp only [star_sum, star_mul', star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z₂ _ => by ring)
  rw [hlhs_z]
  let S_σ : Bool → Bool → ℂ := fun b₁ b₁' =>
    ∑ b₀ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
      σ (r₁, patchWires w y₁ ![b₀, b₁, b₂, b₃])
        (r₂, patchWires w y₂ ![b₀, b₁', b₂, b₃])
  have hσ_expand : ∀ (z₁ z₂ : Qubits 4),
      σ (r₁, patchWires w y₁ z₁) (r₂, patchWires w y₂ z₂) =
        S_σ (z₁ 1) (z₂ 1) *
          (resourceVec θ (z₁ 0) * plusVec (z₁ 2) * basisVec false (z₁ 3)) *
          star (resourceVec θ (z₂ 0) * plusVec (z₂ 2) * basisVec false (z₂ 3)) := by
    intro z₁ z₂
    have step0 := congrFun (congrFun h0 (r₁, patchWires w y₁ z₁)) (r₂, patchWires w y₂ z₂)
    simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_patchWires,
      patchWires_apply_w] at step0
    rw [← step0]
    have step2 : ∀ b₀ : Bool,
        σ (r₁, patchWires w y₁ (t9_setWire 0 b₀ z₁))
          (r₂, patchWires w y₂ (t9_setWire 0 b₀ z₂)) =
        (∑ b₂ : Bool,
          σ (r₁, patchWires w y₁ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₁)))
            (r₂, patchWires w y₂ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₂)))) *
          plusVec (z₁ 2) * star (plusVec (z₂ 2)) := by
      intro b₀
      have s := congrFun (congrFun h2 (r₁, patchWires w y₁ (t9_setWire 0 b₀ z₁)))
        (r₂, patchWires w y₂ (t9_setWire 0 b₀ z₂))
      simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_patchWires,
        patchWires_apply_w, setWire_of_ne (by decide : (2 : Fin 4) ≠ 0)] at s
      exact s.symm
    have step3 : ∀ b₀ b₂ : Bool,
        σ (r₁, patchWires w y₁ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₁)))
          (r₂, patchWires w y₂ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₂))) =
        (∑ b₃ : Bool,
          σ (r₁, patchWires w y₁ ![b₀, z₁ 1, b₂, b₃])
            (r₂, patchWires w y₂ ![b₀, z₂ 1, b₂, b₃])) *
          basisVec false (z₁ 3) * star (basisVec false (z₂ 3)) := by
      intro b₀ b₂
      have s := congrFun (congrFun h3 (r₁, patchWires w y₁ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₁))))
        (r₂, patchWires w y₂ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z₂)))
      simp only [t9_traceAndSetWire, Matrix.of_apply, setWire_patchWires,
        patchWires_apply_w, setWire_of_ne (by decide : (3 : Fin 4) ≠ 2),
        setWire_of_ne (by decide : (3 : Fin 4) ≠ 0)] at s
      have hvec : ∀ (z : Qubits 4) (b₃ : Bool),
          t9_setWire 3 b₃ (t9_setWire 2 b₂ (t9_setWire 0 b₀ z)) = ![b₀, z 1, b₂, b₃] := by
        intro z b₃
        funext i
        fin_cases i <;> simp [setWire_self, setWire_of_ne]
      simp_rw [hvec] at s
      exact s.symm
    simp_rw [step2, step3]
    dsimp only [S_σ]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b₀ _ =>
      Finset.sum_congr rfl (fun b₂ _ =>
        Finset.sum_congr rfl (fun b₃ _ => by simp only [star_mul']; ring)))
  have hlhs_expand :
      (∑ z₁ : Qubits 4, ∑ z₂ : Qubits 4,
        U (y₁ ∘ w) z₁ * σ (r₁, patchWires w y₁ z₁) (r₂, patchWires w y₂ z₂) *
          star (U (y₂ ∘ w) z₂)) =
      ∑ z₁ : Qubits 4, ∑ z₂ : Qubits 4, ∑ b₁ : Bool, ∑ b₁' : Bool,
        S_σ b₁ b₁' *
          (U (y₁ ∘ w) z₁ * vec4 (resourceVec θ) (basisVec b₁) plusVec (basisVec false) z₁) *
          star (U (y₂ ∘ w) z₂ * vec4 (resourceVec θ) (basisVec b₁') plusVec (basisVec false) z₂) := by
    refine Finset.sum_congr rfl (fun z₁ _ => Finset.sum_congr rfl (fun z₂ _ => ?_))
    rw [hσ_expand z₁ z₂]
    have h1 : ∀ b₁' : Bool,
        (∑ b₁ : Bool, S_σ b₁ b₁' *
          (U (y₁ ∘ w) z₁ * vec4 (resourceVec θ) (basisVec b₁) plusVec (basisVec false) z₁)) =
        S_σ (z₁ 1) b₁' *
          (U (y₁ ∘ w) z₁ * (resourceVec θ (z₁ 0) * plusVec (z₁ 2) * basisVec false (z₁ 3))) := by
      intro b₁'
      rw [Fintype.sum_bool]
      cases hz : z₁ 1
      · simp [vec4, basisVec, hz]
      · simp [vec4, basisVec, hz]
    have h2' :
        (∑ b₁ : Bool, ∑ b₁' : Bool, S_σ b₁ b₁' *
          (U (y₁ ∘ w) z₁ * vec4 (resourceVec θ) (basisVec b₁) plusVec (basisVec false) z₁) *
          star (U (y₂ ∘ w) z₂ * vec4 (resourceVec θ) (basisVec b₁') plusVec (basisVec false) z₂)) =
        ∑ b₁' : Bool,
          (∑ b₁ : Bool, S_σ b₁ b₁' *
            (U (y₁ ∘ w) z₁ * vec4 (resourceVec θ) (basisVec b₁) plusVec (basisVec false) z₁)) *
            star (U (y₂ ∘ w) z₂ * vec4 (resourceVec θ) (basisVec b₁') plusVec (basisVec false) z₂) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b₁' _ => (Finset.sum_mul _ _ _).symm)
    rw [h2']
    simp_rw [h1]
    rw [Fintype.sum_bool]
    cases hz : z₂ 1
    · simp only [vec4, basisVec, hz, Bool.false_eq_true, ↓reduceIte,
        mul_zero, zero_mul, star_zero, zero_add, mul_one, star_mul']
      ring
    · simp only [vec4, basisVec, hz, Bool.true_eq_false, ↓reduceIte,
        mul_zero, zero_mul, star_zero, add_zero, mul_one, star_mul']
      ring
  rw [hlhs_expand, sum_factor_2]
  have hprop : ∀ b : Bool,
      (∑ z : Qubits 4, U (y₁ ∘ w) z * vec4 (resourceVec θ) (basisVec b) plusVec (basisVec false) z) =
        vec4 (resourceVec θ) ((rot θ).mulVec (basisVec b)) (resourceVec θ) (basisVec false) (y₁ ∘ w) :=
    fun b => congrFun (proposition_16 θ (basisVec b) plusVec) (y₁ ∘ w)
  have hprop2 : ∀ b : Bool,
      (∑ z : Qubits 4, U (y₂ ∘ w) z * vec4 (resourceVec θ) (basisVec b) plusVec (basisVec false) z) =
        vec4 (resourceVec θ) ((rot θ).mulVec (basisVec b)) (resourceVec θ) (basisVec false) (y₂ ∘ w) :=
    fun b => congrFun (proposition_16 θ (basisVec b) plusVec) (y₂ ∘ w)
  simp_rw [hprop, hprop2]
  rw [Fintype.sum_eq_single (y₁ (w 1)) (fun b₁ hb₁ => by
    simp [vec4, vec4_rot_basisVec_apply, basisVec, hb₁.symm])]
  rw [Fintype.sum_eq_single (y₂ (w 1)) (fun b₁' hb₁' => by
    simp [vec4, vec4_rot_basisVec_apply, basisVec, hb₁'.symm])]
  simp only [vec4, Function.comp_apply, vec4_rot_basisVec_apply, basisVec, ↓reduceIte, mul_one]
  -- Now evaluate RHS!
  rw [Fintype.sum_eq_single y₁ (fun x₁ hx₁ => by simp [t9_rotOnWire_apply, hx₁.symm])]
  rw [Fintype.sum_eq_single y₂ (fun x₂ hx₂ => by simp [t9_rotOnWire_apply, hx₂.symm])]
  simp only [t9_rotOnWire_apply, ↓reduceIte, t9_traceAndSetWire, Matrix.of_apply]
  have hrhs_expand : ∀ b₂ : Bool,
      σ (r₁, t9_setWire (w 2) b₂ y₁) (r₂, t9_setWire (w 2) b₂ y₂) =
        (∑ b₀ : Bool, ∑ b₃ : Bool,
          σ (r₁, patchWires w y₁ ![b₀, y₁ (w 1), b₂, b₃])
            (r₂, patchWires w y₂ ![b₀, y₂ (w 1), b₂, b₃])) *
          (resourceVec θ (y₁ (w 0)) * basisVec false (y₁ (w 3))) *
          star (resourceVec θ (y₂ (w 0)) * basisVec false (y₂ (w 3))) := by
    intro b₂
    have step0 := congrFun (congrFun h0 (r₁, t9_setWire (w 2) b₂ y₁)) (r₂, t9_setWire (w 2) b₂ y₂)
    simp only [t9_traceAndSetWire, Matrix.of_apply,
      setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (0 : Fin 4) ≠ 2))] at step0
    rw [← step0]
    have step3 : ∀ b₀ : Bool,
        σ (r₁, t9_setWire (w 0) b₀ (t9_setWire (w 2) b₂ y₁))
          (r₂, t9_setWire (w 0) b₀ (t9_setWire (w 2) b₂ y₂)) =
        (∑ b₃ : Bool,
          σ (r₁, patchWires w y₁ ![b₀, y₁ (w 1), b₂, b₃])
            (r₂, patchWires w y₂ ![b₀, y₂ (w 1), b₂, b₃])) *
          basisVec false (y₁ (w 3)) * star (basisVec false (y₂ (w 3))) := by
      intro b₀
      have s := congrFun (congrFun h3 (r₁, t9_setWire (w 0) b₀ (t9_setWire (w 2) b₂ y₁)))
        (r₂, t9_setWire (w 0) b₀ (t9_setWire (w 2) b₂ y₂))
      simp only [t9_traceAndSetWire, Matrix.of_apply,
        setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (3 : Fin 4) ≠ 0)),
        setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (3 : Fin 4) ≠ 2))] at s
      have hpatch : ∀ (y : Qubits N) (b₃ : Bool),
          t9_setWire (w 3) b₃ (t9_setWire (w 0) b₀ (t9_setWire (w 2) b₂ y)) =
            patchWires w y ![b₀, y (w 1), b₂, b₃] := by
        intro y b₃
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨i, rfl⟩
          rw [patchWires_apply_w]
          fin_cases i
          · simp [setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (0 : Fin 4) ≠ 3)),
              setWire_self]
          · simp [setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (1 : Fin 4) ≠ 3)),
              setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (1 : Fin 4) ≠ 0)),
              setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (1 : Fin 4) ≠ 2))]
          · simp [setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (2 : Fin 4) ≠ 3)),
              setWire_of_ne (fun h => by exact absurd (w.injective h) (by decide : (2 : Fin 4) ≠ 0)),
              setWire_self]
          · simp [setWire_self]
        · have hne3 : a ≠ w 3 := fun h => ha ⟨3, h.symm⟩
          have hne0 : a ≠ w 0 := fun h => ha ⟨0, h.symm⟩
          have hne2 : a ≠ w 2 := fun h => ha ⟨2, h.symm⟩
          rw [patchWires_apply_not_mem w y _ ha, setWire_of_ne hne3, setWire_of_ne hne0,
            setWire_of_ne hne2]
      simp_rw [hpatch] at s
      exact s.symm
    simp_rw [step3]
    simp_rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun b₀ _ => Finset.sum_congr rfl (fun b₃ _ => by
      simp only [star_mul']; ring))
  simp_rw [hrhs_expand]
  have hswap_sum :
      S_σ (y₁ (w 1)) (y₂ (w 1)) =
      ∑ b₂ : Bool, ∑ b₀ : Bool, ∑ b₃ : Bool,
        σ (r₁, patchWires w y₁ ![b₀, y₁ (w 1), b₂, b₃])
          (r₂, patchWires w y₂ ![b₀, y₂ (w 1), b₂, b₃]) :=
    Finset.sum_comm
  rw [hswap_sum]
  simp only [star_mul', ← Finset.sum_mul, basisVec]
  ring

end Thm9Step2Helpers

theorem t9_step2_api : Thm9Step2API where
  hasPureWire_productAncVec_left := hasPureWire_productAncVec_left_aux
  hasPureWire_productAncVec_right := hasPureWire_productAncVec_right_aux
  hasPureWire_traceAndSet_self := hasPureWire_traceAndSet_self_aux
  hasPureWire_traceAndSet_other := hasPureWire_traceAndSet_other_aux
  traceAndSetWire_unitConj_embedOp := traceAndSetWire_unitConj_embedOp_aux
  traceAndSetWire_unitConj_proj := traceAndSetWire_unitConj_proj_aux
  partialTraceAnc_traceAndSetWire := partialTraceAnc_traceAndSetWire_aux
  norm_sq_resourceVec := norm_sq_resourceVec_aux
  norm_sq_plusVec := norm_sq_plusVec_aux
  norm_sq_basisVec := norm_sq_basisVec_aux
  rotOnWire_zero := rotOnWire_zero_aux
  rotOnWire_two_pi_nat := rotOnWire_two_pi_nat_aux
  rotOnWire_add := rotOnWire_add_aux
  stateInjection_step := stateInjection_step_aux
  phaseHalving_split := phaseHalving_split_aux

section Thm9Step3Helpers

open QAlgorithms ConstOverheadCompile.Main

/-! ### Block A: Matrix, embedding, circuit, and trace-preserving helpers -/

private theorem s3_embedOp_trans {k m n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ)
    (u : Fin k ↪ Fin m) (w : Fin m ↪ Fin n) :
    embedOp (embedOp M u) w = embedOp M (u.trans w) := by
  ext y z
  simp only [embedOp, Matrix.of_apply]
  by_cases hR : ∀ a : Fin n, a ∉ Set.range (u.trans w) → y a = z a
  · rw [if_pos hR]
    have hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a := by
      intro a ha
      apply hR a
      rintro ⟨c, hc⟩
      exact ha ⟨u c, hc⟩
    have hu : ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b) := by
      intro b hb
      apply hR (w b)
      rintro ⟨c, hc⟩
      exact hb ⟨c, w.injective hc⟩
    rw [if_pos hw]
    change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
      then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = _
    rw [if_pos hu]
  · rw [if_neg hR]
    simp only [not_forall] at hR
    rcases hR with ⟨a, ha, hne⟩
    by_cases haw : a ∈ Set.range w
    · rcases haw with ⟨b, rfl⟩
      have hbu : b ∉ Set.range u := by
        rintro ⟨c, rfl⟩
        exact ha ⟨c, rfl⟩
      by_cases hw : ∀ a : Fin n, a ∉ Set.range w → y a = z a
      · rw [if_pos hw]
        change (if ∀ b : Fin m, b ∉ Set.range u → y (w b) = z (w b)
          then M (y ∘ u.trans w) (z ∘ u.trans w) else 0) = 0
        rw [if_neg (fun hu => hne (hu b hbu))]
      · rw [if_neg hw]
    · rw [if_neg (fun hw => hne (hw a haw))]

private theorem s3_embedOp_mul {m n : ℕ} (A B : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp (A * B) w = embedOp A w * embedOp B w := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.mul_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have hsum : (∑ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0)) =
        ∑ x : Qubits n,
          if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
            A (y ∘ w) (x ∘ w) * B (x ∘ w) (z ∘ w) else 0 := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have hxz : ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun a ha =>
          (hyx a ha).symm.trans (hyz a ha)
        rw [if_pos hyx, if_pos hxz, if_pos hyx]
      · rw [if_neg hyx, zero_mul, if_neg hyx]
    rw [hsum, ← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun x _ => x ∘ w)
      (fun _ _ => Finset.mem_univ _)
      (fun x₁ hx₁ x₂ hx₂ h => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
        funext a
        by_cases ha : a ∈ Set.range w
        · rcases ha with ⟨b, rfl⟩
          exact congrFun h b
        · exact (hx₁ a ha).symm.trans (hx₂ a ha))
      (fun x' _ => by
        refine ⟨fun a => if h : ∃ b : Fin m, w b = a then x' (Classical.choose h) else y a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro a ha
          have hnot : ¬ ∃ b : Fin m, w b = a := by simpa [Set.mem_range] using ha
          simp [hnot]
        · funext b
          have h : ∃ b' : Fin m, w b' = w b := ⟨b, rfl⟩
          simp only [Function.comp_apply, h, ↓reduceDIte]
          exact congrArg x' (w.injective (Classical.choose_spec h)))
      (fun _ _ => rfl)
  · rw [if_neg hyz]
    symm
    refine Finset.sum_eq_zero (fun x _ => ?_)
    by_cases hyx : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have hxz : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a := fun hxz =>
        hyz (fun a ha => (hyx a ha).trans (hxz a ha))
      rw [if_neg hxz, mul_zero]
    · rw [if_neg hyx, zero_mul]

private theorem s3_embedOp_conjTranspose {m n : ℕ} (M : Matrix (Qubits m) (Qubits m) ℂ)
    (w : Fin m ↪ Fin n) :
    embedOp Mᴴ w = (embedOp M w)ᴴ := by
  ext y z
  simp only [embedOp, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hiff : (∀ a : Fin n, a ∉ Set.range w → y a = z a) ↔
      (∀ a : Fin n, a ∉ Set.range w → z a = y a) :=
    ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (mt hiff.mpr h), star_zero]

private theorem s3_embedOp_isUnitary {m n : ℕ} {M : Matrix (Qubits m) (Qubits m) ℂ}
    (hM : M ∈ Matrix.unitaryGroup (Qubits m) ℂ) (w : Fin m ↪ Fin n) :
    embedOp M w ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  change M * Mᴴ = 1 at hM
  change embedOp M w * (embedOp M w)ᴴ = 1
  rw [← s3_embedOp_conjTranspose, ← s3_embedOp_mul, hM, embedOp_one]

private theorem s3_embedOp_of_gate_eq {n : ℕ} {g₁ g₂ : Gate} (h : g₁ = g₂)
    (w₁ : Fin g₁.arity ↪ Fin n) (w₂ : Fin g₂.arity ↪ Fin n)
    (hw : ∀ i : Fin g₂.arity, w₁ (i.cast (congrArg Gate.arity h).symm) = w₂ i) :
    embedOp g₁.mat w₁ = embedOp g₂.mat w₂ := by
  subst h
  have : w₁ = w₂ := DFunLike.ext w₁ w₂ hw
  subst this
  rfl

private theorem s3_kronecker_conjTranspose {α β : Type*}
    (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp [Matrix.conjTranspose_apply]

private theorem s3_kronecker_one_isUnitary {m n : ℕ} {U : Matrix (Qubits n) (Qubits n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) ∈ Matrix.unitaryGroup (Fin m × Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hU ⊢
  change U * Uᴴ = 1 at hU
  change ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U) * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ U)ᴴ = 1
  rw [s3_kronecker_conjTranspose, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, mul_one, hU, Matrix.one_kronecker_one]

private theorem s3_ofMatrix1_isUnitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) :
    (Gate.ofMatrix1 M).IsUnitary := by
  rw [Gate.IsUnitary, Matrix.mem_unitaryGroup_iff]
  rw [Matrix.mem_unitaryGroup_iff] at hM
  change M * Mᴴ = 1 at hM
  let e : Qubits 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun b _ => b
      left_inv := fun b => funext fun i => by rw [Fin.eq_zero i]
      right_inv := fun _ => rfl }
  change (M.submatrix e e) * (M.submatrix e e)ᴴ = 1
  have hsub : (M.submatrix e e)ᴴ = Mᴴ.submatrix e e := rfl
  rw [hsub, Matrix.submatrix_mul_equiv M Mᴴ e e e, hM, Matrix.submatrix_one_equiv]

private theorem s3_rot_isUnitary (θ : ℝ) : (Gate.ofMatrix1 (rot θ)).IsUnitary := by
  apply s3_ofMatrix1_isUnitary
  rw [Matrix.mem_unitaryGroup_iff]
  change rot θ * (rot θ)ᴴ = 1
  have hdiag : (rot θ)ᴴ =
      Matrix.diagonal (fun x => if x then star (Complex.exp ((θ : ℂ) * Complex.I)) else 1) := by
    ext x y
    simp only [rot, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : x = y
    · subst h; simp; split_ifs <;> simp
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [hdiag, rot, Matrix.diagonal_mul_diagonal]
  ext a b
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte]
    cases a
    · simp
    · simp only [↓reduceIte, Complex.star_def]
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm,
        Complex.norm_exp_ofReal_mul_I, one_pow, Complex.ofReal_one]
  · simp [h]

private theorem s3_rotOnWire_isUnitary {N : ℕ} (θ : ℝ) (q : Fin N) :
    t9_rotOnWire θ q ∈ Matrix.unitaryGroup (Qubits N) ℂ :=
  s3_embedOp_isUnitary (s3_rot_isUnitary θ) _

private def s3_liftCircuit {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) : Circuit S n :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans w⟩

private theorem s3_liftCircuit_size {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) : (s3_liftCircuit w c).size = c.size :=
  List.length_map _

private theorem s3_unitary_nil {S : Set Gate} {n : ℕ} :
    Circuit.unitary ([] : Circuit S n) = 1 := rfl

private theorem s3_unitary_cons {S : Set Gate} {n : ℕ} (g : GateApp S n) (cs : Circuit S n) :
    Circuit.unitary (g :: cs) = Circuit.unitary cs * embedOp g.gate.mat g.wires := by
  simp [Circuit.unitary]

private theorem s3_liftCircuit_unitary {S : Set Gate} {k n : ℕ} (w : Fin k ↪ Fin n)
    (c : Circuit S k) :
    (s3_liftCircuit w c).unitary = embedOp c.unitary w := by
  induction c with
  | nil => rw [s3_liftCircuit, List.map_nil, s3_unitary_nil, s3_unitary_nil, embedOp_one]
  | cons g cs ih =>
      dsimp only [s3_liftCircuit]
      rw [List.map_cons, s3_unitary_cons]
      change Circuit.unitary (s3_liftCircuit w cs) *
          embedOp g.gate.mat (g.wires.trans w) = _
      rw [ih, ← s3_embedOp_trans, ← s3_embedOp_mul, s3_unitary_cons]

private theorem s3_circuit_unitary_isUnitary {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (c : Circuit S n) :
    c.unitary ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  induction c with
  | nil => rw [s3_unitary_nil]; exact one_mem _
  | cons g cs ih =>
      rw [s3_unitary_cons]
      exact mul_mem ih (s3_embedOp_isUnitary (hS g.gate g.mem) g.wires)

private theorem s3_isHermitian_real_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    ((c : ℂ) • X).IsHermitian := by
  change ((c : ℂ) • X)ᴴ = (c : ℂ) • X
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX.eq]

private theorem s3_unitConj_one {N m_ref : ℕ}
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj (1 : Matrix (Qubits N) (Qubits N) ℂ) σ = σ := by
  simp [t9_unitConj]

private theorem s3_unitConj_mul {N m_ref : ℕ}
    (U₂ U₁ : Matrix (Qubits N) (Qubits N) ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj (U₂ * U₁) σ = t9_unitConj U₂ (t9_unitConj U₁ σ) := by
  dsimp only [t9_unitConj]
  have h1 : (1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ (U₂ * U₁) =
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ U₂) *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ U₁) := by
    rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [h1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem s3_unitConj_smul {N m_ref : ℕ}
    (U : Matrix (Qubits N) (Qubits N) ℂ) (c : ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj U (c • σ) = c • t9_unitConj U σ := by
  dsimp only [t9_unitConj]
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem s3_isDensityOperator_unitConj {N m_ref : ℕ} (s1 : Thm9Step1API)
    {U : Matrix (Qubits N) (Qubits N) ℂ} (hU : U ∈ Matrix.unitaryGroup (Qubits N) ℂ)
    {σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ}
    (hσ : WildeQIT.IsDensityOperator σ) :
    WildeQIT.IsDensityOperator (t9_unitConj U σ) :=
  s1.isDensityOperator_conj_unitary hσ (s3_kronecker_one_isUnitary hU)

private theorem s3_list_sum_map_smul {α M : Type*} [AddCommMonoid M]
    [Module ℂ M] (l : List α) (c : ℂ) (f : α → M) :
    (l.map fun x => c • f x).sum = c • (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, smul_add]

private theorem s3_channelRef_smul {S : Set Gate} {n : ℕ} (B : AdaptiveCircuit S n) (m : ℕ)
    (c : ℂ) (A : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    B.channelRef m (c • A) = c • B.channelRef m A := by
  dsimp only [AdaptiveCircuit.channelRef]
  rw [← s3_list_sum_map_smul]
  congr 1
  refine List.map_congr_left (fun K _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul]

private theorem s3_channelRef_gate {S : Set Gate} {n : ℕ}
    (g : GateApp S n) (k : AdaptiveCircuit S n) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    (AdaptiveCircuit.gate g k).channelRef m ρ =
      k.channelRef m (t9_unitConj (embedOp g.gate.mat g.wires) ρ) := by
  dsimp only [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList, t9_unitConj]
  rw [List.map_map]
  congr 1
  refine List.map_congr_left (fun K _ => ?_)
  dsimp only [Function.comp_apply]
  have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * embedOp g.gate.mat g.wires) =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ embedOp g.gate.mat g.wires) := by
    rw [← Matrix.mul_kronecker_mul, one_mul]
  rw [h1, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

private theorem s3_channelRef_measure {S : Set Gate} {n : ℕ}
    (q : Fin n) (k : Bool → AdaptiveCircuit S n) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    (AdaptiveCircuit.measure q k).channelRef m ρ =
      (k false).channelRef m (t9_unitConj (AdaptiveCircuit.proj q false) ρ) +
      (k true).channelRef m (t9_unitConj (AdaptiveCircuit.proj q true) ρ) := by
  dsimp only [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList, t9_unitConj]
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  congr 1
  · congr 1
    refine List.map_congr_left (fun K _ => ?_)
    dsimp only [Function.comp_apply]
    have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * AdaptiveCircuit.proj q false) =
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q false) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [h1, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · congr 1
    refine List.map_congr_left (fun K _ => ?_)
    dsimp only [Function.comp_apply]
    have h1 : (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (K * AdaptiveCircuit.proj q true) =
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) *
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ AdaptiveCircuit.proj q true) := by
      rw [← Matrix.mul_kronecker_mul, one_mul]
    rw [h1, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]

private theorem s3_channelRef_prependCircuit {S : Set Gate} {n : ℕ}
    (c : Circuit S n) (B : AdaptiveCircuit S n) (m : ℕ)
    (σ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    (t9_prependCircuit c B).channelRef m σ = B.channelRef m (t9_unitConj c.unitary σ) := by
  induction c generalizing σ with
  | nil => rw [t9_prependCircuit, List.foldr_nil, s3_unitary_nil, s3_unitConj_one]
  | cons g gs ih =>
      dsimp only [t9_prependCircuit]
      rw [List.foldr_cons]
      change (AdaptiveCircuit.gate g (t9_prependCircuit gs B)).channelRef m σ = _
      rw [s3_channelRef_gate, ih, s3_unitary_cons, s3_unitConj_mul]

private theorem s3_proj_conjTranspose {n : ℕ} (q : Fin n) (b : Bool) :
    (AdaptiveCircuit.proj q b)ᴴ = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

private theorem s3_proj_mul_self {n : ℕ} (q : Fin n) (b : Bool) :
    AdaptiveCircuit.proj q b * AdaptiveCircuit.proj q b = AdaptiveCircuit.proj q b := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem s3_proj_add {n : ℕ} (q : Fin n) :
    AdaptiveCircuit.proj q false + AdaptiveCircuit.proj q true = 1 := by
  ext y z
  simp only [AdaptiveCircuit.proj, Matrix.add_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : y = z
  · subst h; cases y q <;> simp
  · simp [h]

private theorem s3_list_sum_map_mul_left_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : List (Matrix ι ι ℂ)) (A B : Matrix ι ι ℂ) :
    (l.map fun K => A * K * B).sum = A * l.sum * B := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Matrix.mul_add, Matrix.add_mul]

private theorem s3_krausList_sum_conj_mul {S : Set Gate} {n : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n) :
    (B.krausList.map fun K => Kᴴ * K).sum = 1 := by
  induction B with
  | done => simp [AdaptiveCircuit.krausList]
  | gate g k ih =>
      have hU : embedOp g.gate.mat g.wires ∈ Matrix.unitaryGroup (Qubits n) ℂ :=
        s3_embedOp_isUnitary (hS g.gate g.mem) g.wires
      rw [Matrix.mem_unitaryGroup_iff'] at hU
      change (embedOp g.gate.mat g.wires)ᴴ * embedOp g.gate.mat g.wires = 1 at hU
      simp only [AdaptiveCircuit.krausList, List.map_map]
      have hcongr :
          (k.krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * embedOp g.gate.mat g.wires)) =
          ((k.krausList.map fun x => xᴴ * x).map fun K =>
            (embedOp g.gate.mat g.wires)ᴴ * K * embedOp g.gate.mat g.wires) := by
        rw [List.map_map]
        refine List.map_congr_left (fun x _ => ?_)
        simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [hcongr, s3_list_sum_map_mul_left_right, ih, Matrix.mul_one, hU]
  | measure q k ih =>
      simp only [AdaptiveCircuit.krausList, List.map_append, List.sum_append, List.map_map]
      have hbranch : ∀ b : Bool,
          ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)).sum =
            AdaptiveCircuit.proj q b := by
        intro b
        have hcongr :
            ((k b).krausList.map ((fun K => Kᴴ * K) ∘ fun K => K * AdaptiveCircuit.proj q b)) =
            (((k b).krausList.map fun x => xᴴ * x).map fun K =>
              (AdaptiveCircuit.proj q b)ᴴ * K * AdaptiveCircuit.proj q b) := by
          rw [List.map_map]
          refine List.map_congr_left (fun x _ => ?_)
          simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]
        rw [hcongr, s3_list_sum_map_mul_left_right, ih b, Matrix.mul_one,
          s3_proj_conjTranspose, s3_proj_mul_self]
      rw [hbranch false, hbranch true, s3_proj_add]

private theorem s3_isDensityOperator_channelRef {S : Set Gate} {n m : ℕ}
    (hS : ∀ g ∈ S, g.IsUnitary) (B : AdaptiveCircuit S n)
    {ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ}
    (hρ : WildeQIT.IsDensityOperator ρ) :
    WildeQIT.IsDensityOperator (B.channelRef m ρ) := by
  dsimp only [AdaptiveCircuit.channelRef]
  refine ⟨?_, ?_⟩
  · have hsum : ∀ (l : List (Matrix (Qubits n) (Qubits n) ℂ)),
        (l.map fun K =>
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * ρ *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum.PosSemidef := by
      intro l
      induction l with
      | nil => simpa using Matrix.PosSemidef.zero
      | cons K Ks ih =>
          simp only [List.map_cons, List.sum_cons]
          exact (hρ.1.mul_mul_conjTranspose_same _).add ih
    exact hsum B.krausList
  · have htr : ∀ (l : List (Matrix (Qubits n) (Qubits n) ℂ)),
        (l.map fun K =>
          ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * ρ *
            ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum.trace =
        (((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (l.map fun K => Kᴴ * K).sum) * ρ).trace := by
      intro l
      induction l with
      | nil => simp
      | cons K Ks ih =>
          simp only [List.map_cons, List.sum_cons, Matrix.trace_add, ih,
            Matrix.kronecker_add, Matrix.add_mul]
          congr 1
          rw [Matrix.trace_mul_cycle, s3_kronecker_conjTranspose, Matrix.conjTranspose_one,
            ← Matrix.mul_kronecker_mul, one_mul]
    rw [htr B.krausList, s3_krausList_sum_conj_mul hS B, Matrix.one_kronecker_one, one_mul, hρ.2]

private theorem s3_gridGates_isUnitary (D : ℕ) :
    ∀ g ∈ gridGates D, g.IsUnitary := by
  rintro g ⟨j, _, rfl⟩
  exact s3_rot_isUnitary _

private theorem s3_cliffordT_union_gridGates_isUnitary (s1 : Thm9Step1API) (D : ℕ) :
    ∀ g ∈ CliffordT ∪ gridGates D, g.IsUnitary := by
  rintro g (hg | hg)
  · exact s1.cliffordT_isUnitary g hg
  · exact s3_gridGates_isUnitary D g hg

private theorem s3_partialTraceAnc_smul {n a m_ref : ℕ} (c : ℂ)
    (σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (c • σ) = c • t9_partialTraceAnc σ := by
  ext p₁ p₂
  simp [t9_partialTraceAnc, Finset.mul_sum]

private theorem s3_partialTraceAnc_add {n a m_ref : ℕ}
    (σ₁ σ₂ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (σ₁ + σ₂) = t9_partialTraceAnc σ₁ + t9_partialTraceAnc σ₂ := by
  ext p₁ p₂
  simp [t9_partialTraceAnc, Finset.sum_add_distrib]

private theorem s3_partialTraceAnc_sub {n a m_ref : ℕ}
    (σ₁ σ₂ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (σ₁ - σ₂) = t9_partialTraceAnc σ₁ - t9_partialTraceAnc σ₂ := by
  ext p₁ p₂
  simp [t9_partialTraceAnc, Finset.sum_sub_distrib]

private theorem s3_qubits_add_sum {n a : ℕ} (f : Qubits (n + a) → ℂ) :
    (∑ x : Qubits (n + a), f x) = ∑ x : Qubits n, ∑ j : Qubits a, f (Fin.append x j) := by
  let e : Qubits n × Qubits a ≃ Qubits (n + a) :=
    { toFun := fun p => Fin.append p.1 p.2
      invFun := fun u => (fun i => u (Fin.castAdd a i), fun j => u (Fin.natAdd n j))
      left_inv := fun p => Prod.ext
        (funext fun i => by simp [Fin.append_left])
        (funext fun j => by simp [Fin.append_right])
      right_inv := fun u => by
        funext k
        refine Fin.addCases (fun i => ?_) (fun j => ?_) k
        · simp [Fin.append_left]
        · simp [Fin.append_right] }
  rw [← Fintype.sum_equiv e (fun p => f (Fin.append p.1 p.2)) f (fun _ => rfl)]
  exact Fintype.sum_prod_type _

private theorem s3_partialTraceAnc_unitConj_data {n a m_ref : ℕ}
    (K : Matrix (Qubits n) (Qubits n) ℂ)
    (K_big : Matrix (Qubits (n + a)) (Qubits (n + a)) ℂ)
    (hK : ∀ (y₁ y₂ : Qubits n) (z₁ z₂ : Qubits a),
      K_big (Fin.append y₁ z₁) (Fin.append y₂ z₂) = if z₁ = z₂ then K y₁ y₂ else 0)
    (σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (t9_unitConj K_big σ) = t9_unitConj K (t9_partialTraceAnc σ) := by
  ext ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
  simp only [t9_partialTraceAnc, t9_unitConj, Matrix.of_apply, Matrix.mul_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  have hL : ∀ j : Qubits a,
      (∑ i₃ : Fin m_ref, ∑ u₁ : Qubits (n + a),
        (∑ i₄ : Fin m_ref, ∑ u₂ : Qubits (n + a),
          ((if i₁ = i₄ then (1 : ℂ) else 0) * K_big (Fin.append y₁ j) u₂) *
            σ (i₄, u₂) (i₃, u₁)) *
          star ((if i₂ = i₃ then (1 : ℂ) else 0) * K_big (Fin.append y₂ j) u₁)) =
      ∑ x₁ : Qubits n, ∑ x₂ : Qubits n,
        K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) * star (K y₂ x₂) := by
    intro j
    rw [Finset.sum_eq_single i₂
      (fun i₃ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
    simp only [↓reduceIte, one_mul]
    have hi4 : ∀ u₁ : Qubits (n + a),
        (∑ i₄ : Fin m_ref, ∑ u₂ : Qubits (n + a),
          ((if i₁ = i₄ then (1 : ℂ) else 0) * K_big (Fin.append y₁ j) u₂) *
            σ (i₄, u₂) (i₂, u₁)) =
        ∑ u₂ : Qubits (n + a), K_big (Fin.append y₁ j) u₂ * σ (i₁, u₂) (i₂, u₁) := by
      intro u₁
      rw [Finset.sum_eq_single i₁
        (fun i₄ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
      simp only [↓reduceIte, one_mul]
    rw [Finset.sum_congr rfl fun u₁ _ => by rw [hi4 u₁]]
    rw [s3_qubits_add_sum (n := n) (a := a)]
    have hinner : ∀ x₂ : Qubits n, ∀ z₂ : Qubits a,
        (∑ u₂ : Qubits (n + a),
          K_big (Fin.append y₁ j) u₂ * σ (i₁, u₂) (i₂, Fin.append x₂ z₂)) *
          star (K_big (Fin.append y₂ j) (Fin.append x₂ z₂)) =
        if z₂ = j then
          (∑ x₁ : Qubits n, K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
            star (K y₂ x₂)
        else 0 := by
      intro x₂ z₂
      rw [hK y₂ x₂ j z₂]
      by_cases hzj : z₂ = j
      · subst hzj
        simp only [↓reduceIte]
        congr 1
        rw [s3_qubits_add_sum (n := n) (a := a)]
        refine Finset.sum_congr rfl fun x₁ _ => ?_
        have h3 : ∀ z₁ : Qubits a,
            K_big (Fin.append y₁ z₂) (Fin.append x₁ z₁) *
              σ (i₁, Fin.append x₁ z₁) (i₂, Fin.append x₂ z₂) =
            if z₂ = z₁ then K y₁ x₁ * σ (i₁, Fin.append x₁ z₂) (i₂, Fin.append x₂ z₂) else 0 := by
          intro z₁
          rw [hK y₁ x₁ z₂ z₁]
          split_ifs with hzz
          · subst hzz; rfl
          · simp
        rw [Finset.sum_congr rfl fun z₁ _ => h3 z₁, Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ↓reduceIte]
      · have hne : j ≠ z₂ := Ne.symm hzj
        simp [hzj, hne]
    simp_rw [hinner]
    have h4 : ∀ x₂ : Qubits n,
        (∑ z₂ : Qubits a,
          if z₂ = j then
            (∑ x₁ : Qubits n, K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
              star (K y₂ x₂)
          else 0) =
        (∑ x₁ : Qubits n, K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
          star (K y₂ x₂) := by
      intro x₂
      rw [Finset.sum_ite_eq']
      simp
    simp_rw [h4, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => hL j]
  rw [Finset.sum_eq_single i₂
    (fun i₃ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
  simp only [↓reduceIte, one_mul]
  have hi4R : ∀ x₂ : Qubits n,
      (∑ i₄ : Fin m_ref, ∑ x₁ : Qubits n,
        ((if i₁ = i₄ then (1 : ℂ) else 0) * K y₁ x₁) *
          ∑ j : Qubits a, σ (i₄, Fin.append x₁ j) (i₂, Fin.append x₂ j)) =
      ∑ x₁ : Qubits n,
        K y₁ x₁ * ∑ j : Qubits a, σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) := by
    intro x₂
    rw [Finset.sum_eq_single i₁
      (fun i₄ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
    simp only [↓reduceIte, one_mul]
  have hLHS :
      (∑ j : Qubits a, ∑ x₁ : Qubits n, ∑ x₂ : Qubits n,
        K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) * star (K y₂ x₂)) =
      ∑ x₁ : Qubits n, ∑ x₂ : Qubits n, ∑ j : Qubits a,
        K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) * star (K y₂ x₂) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_comm
  have hRHS :
      (∑ x₂ : Qubits n,
        (∑ i₄ : Fin m_ref, ∑ x₁ : Qubits n,
          ((if i₁ = i₄ then (1 : ℂ) else 0) * K y₁ x₁) *
            ∑ j : Qubits a, σ (i₄, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
          star (K y₂ x₂)) =
      ∑ x₁ : Qubits n, ∑ x₂ : Qubits n, ∑ j : Qubits a,
        K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) * star (K y₂ x₂) := by
    have hR1 :
        (∑ x₂ : Qubits n,
          (∑ i₄ : Fin m_ref, ∑ x₁ : Qubits n,
            ((if i₁ = i₄ then (1 : ℂ) else 0) * K y₁ x₁) *
              ∑ j : Qubits a, σ (i₄, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
            star (K y₂ x₂)) =
        ∑ x₂ : Qubits n,
          (∑ x₁ : Qubits n,
            ∑ j : Qubits a, K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
            star (K y₂ x₂) := by
      refine Finset.sum_congr rfl fun x₂ _ => congrArg (· * star (K y₂ x₂)) ?_
      rw [hi4R x₂]
      exact Finset.sum_congr rfl fun x₁ _ => Finset.mul_sum _ _ _
    rw [hR1]
    have hR2 :
        (∑ x₂ : Qubits n,
          (∑ x₁ : Qubits n,
            ∑ j : Qubits a, K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j)) *
            star (K y₂ x₂)) =
        ∑ x₂ : Qubits n, ∑ x₁ : Qubits n, ∑ j : Qubits a,
          K y₁ x₁ * σ (i₁, Fin.append x₁ j) (i₂, Fin.append x₂ j) * star (K y₂ x₂) := by
      refine Finset.sum_congr rfl fun x₂ _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun x₁ _ => Finset.sum_mul _ _ _
    rw [hR2]
    exact Finset.sum_comm
  exact hLHS.trans hRHS.symm

private theorem s3_partialTraceAnc_unitConj_embedOp_data {k n a m_ref : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    (σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc
        (t9_unitConj (embedOp M (w.trans ⟨Fin.castAdd a, Fin.castAdd_injective n a⟩)) σ) =
      t9_unitConj (embedOp M w) (t9_partialTraceAnc σ) := by
  refine s3_partialTraceAnc_unitConj_data (embedOp M w) _ ?_ σ
  intro y₁ y₂ z₁ z₂
  let w_big : Fin k ↪ Fin (n + a) := w.trans ⟨Fin.castAdd a, Fin.castAdd_injective n a⟩
  change (if ∀ q : Fin (n + a), q ∉ Set.range w_big → Fin.append y₁ z₁ q = Fin.append y₂ z₂ q
      then M (Fin.append y₁ z₁ ∘ w_big) (Fin.append y₂ z₂ ∘ w_big) else 0) =
    if z₁ = z₂ then
      (if ∀ i : Fin n, i ∉ Set.range w → y₁ i = y₂ i then M (y₁ ∘ w) (y₂ ∘ w) else 0)
    else 0
  have hcomp : ∀ (y : Qubits n) (z : Qubits a), Fin.append y z ∘ w_big = y ∘ w := by
    intro y z
    funext c
    exact Fin.append_left y z (w c)
  rw [hcomp y₁ z₁, hcomp y₂ z₂]
  have hcond :
      (∀ q : Fin (n + a), q ∉ Set.range w_big → Fin.append y₁ z₁ q = Fin.append y₂ z₂ q) ↔
      (z₁ = z₂ ∧ ∀ i : Fin n, i ∉ Set.range w → y₁ i = y₂ i) := by
    constructor
    · intro h
      refine ⟨funext fun j => ?_, fun i hi => ?_⟩
      · have hj : Fin.natAdd n j ∉ Set.range w_big := by
          rintro ⟨c, hc⟩
          have hc' := congrArg Fin.val hc
          change (Fin.castAdd a (w c)).1 = (Fin.natAdd n j).1 at hc'
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hc'
          omega
        simpa [Fin.append_right] using h (Fin.natAdd n j) hj
      · have hi' : Fin.castAdd a i ∉ Set.range w_big := by
          rintro ⟨c, hc⟩
          exact hi ⟨c, Fin.castAdd_injective n a hc⟩
        simpa [Fin.append_left] using h (Fin.castAdd a i) hi'
    · rintro ⟨hz, hy⟩ q
      refine Fin.addCases (fun i hq => ?_) (fun j _ => ?_) q
      · rw [Fin.append_left, Fin.append_left]
        apply hy i
        rintro ⟨c, rfl⟩
        exact hq ⟨c, rfl⟩
      · rw [Fin.append_right, Fin.append_right, hz]
  by_cases h1 : ∀ q : Fin (n + a), q ∉ Set.range w_big → Fin.append y₁ z₁ q = Fin.append y₂ z₂ q
  · have h2 := hcond.mp h1
    rw [if_pos h1, if_pos h2.1, if_pos h2.2]
  · rw [if_neg h1]
    by_cases hz : z₁ = z₂
    · rw [if_pos hz]
      have hnot : ¬ ∀ i : Fin n, i ∉ Set.range w → y₁ i = y₂ i := fun hy => h1 (hcond.mpr ⟨hz, hy⟩)
      rw [if_neg hnot]
    · rw [if_neg hz]

private theorem s3_partialTraceAnc_unitConj_proj_data {n a m_ref : ℕ}
    (q : Fin n) (b : Bool)
    (σ : Matrix (Fin m_ref × Qubits (n + a)) (Fin m_ref × Qubits (n + a)) ℂ) :
    t9_partialTraceAnc (t9_unitConj (AdaptiveCircuit.proj (Fin.castAdd a q) b) σ) =
      t9_unitConj (AdaptiveCircuit.proj q b) (t9_partialTraceAnc σ) := by
  refine s3_partialTraceAnc_unitConj_data (AdaptiveCircuit.proj q b) _ ?_ σ
  intro y₁ y₂ z₁ z₂
  simp only [AdaptiveCircuit.proj, Matrix.diagonal_apply, Fin.append_left]
  by_cases hy : y₁ = y₂ <;> by_cases hz : z₁ = z₂
  · subst hy; subst hz; simp
  · have hne : Fin.append y₁ z₁ ≠ Fin.append y₂ z₂ := by
      intro h
      apply hz
      funext j
      have := congrFun h (Fin.natAdd n j)
      simpa [Fin.append_right] using this
    simp [hz, hne]
  · have hne : Fin.append y₁ z₁ ≠ Fin.append y₂ z₂ := by
      intro h
      apply hy
      funext i
      have := congrFun h (Fin.castAdd a i)
      simpa [Fin.append_left] using this
    simp [hy, hne]
  · have hne : Fin.append y₁ z₁ ≠ Fin.append y₂ z₂ := by
      intro h
      apply hz
      funext j
      have := congrFun h (Fin.natAdd n j)
      simpa [Fin.append_right] using this
    simp [hz, hne]

private theorem s3_t9_traceAndSetWire_smul {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ)
    (c : ℂ) (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_traceAndSetWire q v (c • σ) = c • t9_traceAndSetWire q v σ := by
  ext p₁ p₂
  simp only [t9_traceAndSetWire, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

private theorem s3_t9_traceAndSetWire_comm {N m_ref : ℕ} {q₁ q₂ : Fin N} (hne : q₁ ≠ q₂)
    (v₁ v₂ : Bool → ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_traceAndSetWire q₁ v₁ (t9_traceAndSetWire q₂ v₂ σ) =
      t9_traceAndSetWire q₂ v₂ (t9_traceAndSetWire q₁ v₁ σ) := by
  have hupd : ∀ (x : Qubits N) (b₁ b₂ : Bool),
      Function.update (Function.update x q₁ b₁) q₂ b₂ =
        Function.update (Function.update x q₂ b₂) q₁ b₁ := by
    intro x b₁ b₂
    funext a
    by_cases h1 : a = q₁ <;> by_cases h2 : a = q₂ <;>
      simp [h1, h2, hne, hne.symm]
  ext p₁ p₂
  simp only [t9_traceAndSetWire, Matrix.of_apply, t9_setWire,
    Function.update_of_ne hne.symm, Function.update_of_ne hne, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₁ _ => ?_
  rw [hupd p₁.2 b₁ b₂, hupd p₂.2 b₁ b₂]
  ring

private def s3_wireResetKraus {N : ℕ} (q : Fin N) (v : Bool → ℂ) (b : Bool) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun y z => if z = t9_setWire q b y then v (y q) else 0

private theorem s3_wireResetKraus_action {N m_ref : ℕ} (q : Fin N) (v : Bool → ℂ)
    (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ) :
    t9_unitConj (s3_wireResetKraus q v false) σ +
      t9_unitConj (s3_wireResetKraus q v true) σ =
    t9_traceAndSetWire q v σ := by
  have hterm : ∀ b : Bool, ∀ p₁ p₂ : Fin m_ref × Qubits N,
      t9_unitConj (s3_wireResetKraus q v b) σ p₁ p₂ =
        σ (p₁.1, t9_setWire q b p₁.2) (p₂.1, t9_setWire q b p₂.2) *
          v (p₁.2 q) * star (v (p₂.2 q)) := by
    intro b ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
    simp only [t9_unitConj, s3_wireResetKraus, Matrix.mul_apply, Matrix.kronecker_apply,
      Matrix.one_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i₂
      (fun i₃ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
    rw [Finset.sum_eq_single (t9_setWire q b y₂)
      (fun u₁ _ hu => by simp [hu]) (fun h => False.elim (h (Finset.mem_univ _)))]
    rw [Finset.sum_eq_single i₁
      (fun i₄ _ hi => by simp [hi.symm]) (fun h => False.elim (h (Finset.mem_univ _)))]
    rw [Finset.sum_eq_single (t9_setWire q b y₁)
      (fun u₂ _ hu => by simp [hu]) (fun h => False.elim (h (Finset.mem_univ _)))]
    simp only [↓reduceIte, one_mul]
    ring
  ext p₁ p₂
  simp only [Matrix.add_apply, t9_traceAndSetWire, Matrix.of_apply, Fintype.sum_bool,
    hterm false p₁ p₂, hterm true p₁ p₂]
  ring

private theorem s3_wireResetKraus_sum_one {N : ℕ} (q : Fin N) (v : Bool → ℂ)
    (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1) :
    (s3_wireResetKraus q v false)ᴴ * s3_wireResetKraus q v false +
      (s3_wireResetKraus q v true)ᴴ * s3_wireResetKraus q v true = 1 := by
  have hnorm : star (v false) * v false + star (v true) * v true = 1 := by
    have hmul : ∀ b : Bool, star (v b) * v b = ((‖v b‖ ^ 2 : ℝ) : ℂ) := by
      intro b
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hmul false, hmul true, ← Complex.ofReal_add, hv, Complex.ofReal_one]
  ext z₁ z₂
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    s3_wireResetKraus, Matrix.of_apply, Matrix.one_apply]
  by_cases hzz : z₁ = z₂
  · subst hzz
    simp only [↓reduceIte]
    have hsplit : ∀ b : Bool,
        (∑ y : Qubits N,
          star (if z₁ = t9_setWire q b y then v (y q) else 0) *
            (if z₁ = t9_setWire q b y then v (y q) else 0)) =
        if z₁ q = b then
          (∑ y : Qubits N,
            if y = t9_setWire q false z₁ ∨ y = t9_setWire q true z₁ then
              star (v (y q)) * v (y q) else 0)
        else 0 := by
      intro b
      by_cases hzb : z₁ q = b
      · rw [if_pos hzb]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hiff : z₁ = t9_setWire q b y ↔
            (y = t9_setWire q false z₁ ∨ y = t9_setWire q true z₁) := by
          constructor
          · intro h
            subst h
            cases hyq : y q
            · left
              funext a
              by_cases ha : a = q
              · subst ha; simp [t9_setWire, hyq]
              · simp [t9_setWire, Function.update_of_ne ha]
            · right
              funext a
              by_cases ha : a = q
              · subst ha; simp [t9_setWire, hyq]
              · simp [t9_setWire, Function.update_of_ne ha]
          · rintro (rfl | rfl)
            · funext a
              by_cases ha : a = q
              · subst ha; simp [t9_setWire, hzb]
              · simp [t9_setWire, Function.update_of_ne ha]
            · funext a
              by_cases ha : a = q
              · subst ha; simp [t9_setWire, hzb]
              · simp [t9_setWire, Function.update_of_ne ha]
        by_cases hy : z₁ = t9_setWire q b y
        · rw [if_pos hy, if_pos (hiff.mp hy)]
        · rw [if_neg hy, if_neg (mt hiff.mpr hy), star_zero, mul_zero]
      · rw [if_neg hzb]
        refine Finset.sum_eq_zero fun y _ => ?_
        have hne : z₁ ≠ t9_setWire q b y := by
          intro h
          apply hzb
          have := congrFun h q
          simpa [t9_setWire] using this
        simp [hne]
    rw [hsplit false, hsplit true]
    have hdisj : t9_setWire q false z₁ ≠ t9_setWire q true z₁ := by
      intro h
      have := congrFun h q
      simp [t9_setWire] at this
    have hpair :
        (∑ y : Qubits N,
          if y = t9_setWire q false z₁ ∨ y = t9_setWire q true z₁ then
            star (v (y q)) * v (y q) else 0) = 1 := by
      have hsep : ∀ y : Qubits N,
          (if y = t9_setWire q false z₁ ∨ y = t9_setWire q true z₁ then
            star (v (y q)) * v (y q) else 0) =
          (if y = t9_setWire q false z₁ then star (v (y q)) * v (y q) else 0) +
          (if y = t9_setWire q true z₁ then star (v (y q)) * v (y q) else 0) := by
        intro y
        by_cases h1 : y = t9_setWire q false z₁
        · subst h1; simp [hdisj]
        · by_cases h2 : y = t9_setWire q true z₁
          · subst h2; simp [h1]
          · simp [h1, h2]
      simp_rw [hsep, Finset.sum_add_distrib]
      have hterm : ∀ b : Bool,
          (∑ y : Qubits N,
            if y = t9_setWire q b z₁ then star (v (y q)) * v (y q) else 0) =
          star (v b) * v b := by
        intro b
        rw [Finset.sum_eq_single (t9_setWire q b z₁)
          (fun y _ hy => if_neg hy) (fun h => False.elim (h (Finset.mem_univ _)))]
        simp [t9_setWire]
      rw [hterm false, hterm true]
      exact hnorm
    rw [hpair]
    cases z₁ q <;> simp
  · simp only [hzz, ↓reduceIte]
    have hzero : ∀ b : Bool,
        (∑ y : Qubits N,
          star (if z₁ = t9_setWire q b y then v (y q) else 0) *
            (if z₂ = t9_setWire q b y then v (y q) else 0)) = 0 := by
      intro b
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases h1 : z₁ = t9_setWire q b y
      · have h2 : z₂ ≠ t9_setWire q b y := fun h2 => hzz (h1.trans h2.symm)
        simp [h1, h2]
      · simp [h1]
    rw [hzero false, hzero true, add_zero]

private theorem s3_t9_traceAndSetWire_isDensityOperator {N m_ref : ℕ}
    (q : Fin N) (v : Bool → ℂ) (hv : ‖v false‖ ^ 2 + ‖v true‖ ^ 2 = 1)
    {σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ}
    (hσ : WildeQIT.IsDensityOperator σ) :
    WildeQIT.IsDensityOperator (t9_traceAndSetWire q v σ) := by
  rw [← s3_wireResetKraus_action q v σ]
  refine ⟨(hσ.1.mul_mul_conjTranspose_same _).add (hσ.1.mul_mul_conjTranspose_same _), ?_⟩
  have htr_conj : ∀ K : Matrix (Qubits N) (Qubits N) ℂ,
      (t9_unitConj K σ).trace =
        (σ * (((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K)ᴴ *
          ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ K))).trace := by
    intro K
    dsimp only [t9_unitConj]
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [Matrix.trace_add, htr_conj, htr_conj, ← Matrix.trace_add, ← Matrix.mul_add]
  have h1 :
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ s3_wireResetKraus q v false)ᴴ *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ s3_wireResetKraus q v false) +
      ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ s3_wireResetKraus q v true)ᴴ *
        ((1 : Matrix (Fin m_ref) (Fin m_ref) ℂ) ⊗ₖ s3_wireResetKraus q v true) = 1 := by
    rw [s3_kronecker_conjTranspose, s3_kronecker_conjTranspose, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, one_mul,
      ← Matrix.kronecker_add, s3_wireResetKraus_sum_one q v hv, Matrix.one_kronecker_one]
  rw [h1, Matrix.mul_one, hσ.2]

private theorem s3_sum_prod_qubits : ∀ (k : ℕ) (f : Fin k → Bool → ℝ),
    (∑ z : Qubits k, ∏ i : Fin k, f i (z i)) = ∏ i : Fin k, (f i false + f i true)
  | 0, f => by
      let e : Unit ≃ Qubits 0 :=
        ⟨fun _ _ => false, fun _ => (), fun _ => rfl, fun z => funext fun i => Fin.elim0 i⟩
      rw [← Fintype.sum_equiv e (fun _ => (1 : ℝ)) (fun z => ∏ i : Fin 0, f i (z i)) (fun _ => by simp)]
      simp
  | k + 1, f => by
      let e : Bool × Qubits k ≃ Qubits (k + 1) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun z => (z 0, Fin.tail z)
          left_inv := fun p => Prod.ext (by simp) (funext fun i => by simp [Fin.tail])
          right_inv := fun z => Fin.cons_self_tail z }
      rw [← Fintype.sum_equiv e
        (fun p => f 0 p.1 * ∏ i : Fin k, f i.succ (p.2 i))
        (fun z => ∏ i : Fin (k + 1), f i (z i))
        (fun p => by
          rw [Fin.prod_univ_succ]
          rfl)]
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, s3_sum_prod_qubits k (fun i => f i.succ)]
      rw [← Finset.sum_mul, Fintype.sum_bool, add_comm (f 0 true), Fin.prod_univ_succ]

private theorem s3_norm_sq_productAncVec (s2 : Thm9Step2API) {L M : ℕ} (α : Fin L → ℝ) :
    (∑ z : Qubits (L + M), ‖t9_productAncVec α z‖ ^ 2) = 1 := by
  let w : Fin (L + M) → Bool → ℝ :=
    Fin.addCases (fun i b => ‖resourceVec (α i) b‖ ^ 2) (fun _ b => ‖basisVec false b‖ ^ 2)
  have hterm : ∀ z : Qubits (L + M),
      ‖t9_productAncVec α z‖ ^ 2 = ∏ k : Fin (L + M), w k (z k) := by
    intro z
    dsimp only [t9_productAncVec]
    rw [norm_mul, mul_pow, norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
      Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [w, Fin.addCases_left]
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp [w, Fin.addCases_right]
  simp_rw [hterm, s3_sum_prod_qubits]
  refine Finset.prod_eq_one fun k _ => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa [w] using s2.norm_sq_resourceVec (α i)
  · simpa [w] using s2.norm_sq_basisVec false

private theorem s3_partialTraceAnc_tensorAncVec {n a m_ref : ℕ}
    {χ : Qubits a → ℂ} (hχ : (∑ z : Qubits a, ‖χ z‖ ^ 2) = 1)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    t9_partialTraceAnc (t9_tensorAncVec χ ρ) = ρ := by
  have hsum : (∑ z : Qubits a, χ z * star (χ z)) = 1 := by
    have hmul : ∀ z : Qubits a, χ z * star (χ z) = ((‖χ z‖ ^ 2 : ℝ) : ℂ) := by
      intro z
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    simp_rw [hmul, ← Complex.ofReal_sum, hχ, Complex.ofReal_one]
  ext ⟨i₁, y₁⟩ ⟨i₂, y₂⟩
  simp only [t9_partialTraceAnc, t9_tensorAncVec, Matrix.of_apply]
  have heq : ∀ j : Qubits a,
      ρ (i₁, fun i => Fin.append y₁ j (Fin.castAdd a i))
        (i₂, fun i => Fin.append y₂ j (Fin.castAdd a i)) *
        χ (fun k => Fin.append y₁ j (Fin.natAdd n k)) *
        star (χ (fun k => Fin.append y₂ j (Fin.natAdd n k))) =
      ρ (i₁, y₁) (i₂, y₂) * (χ j * star (χ j)) := by
    intro j
    have hy1 : (fun i => Fin.append y₁ j (Fin.castAdd a i)) = y₁ :=
      funext fun i => Fin.append_left y₁ j i
    have hy2 : (fun i => Fin.append y₂ j (Fin.castAdd a i)) = y₂ :=
      funext fun i => Fin.append_left y₂ j i
    have hj1 : (fun k => Fin.append y₁ j (Fin.natAdd n k)) = j :=
      funext fun k => Fin.append_right y₁ j k
    have hj2 : (fun k => Fin.append y₂ j (Fin.natAdd n k)) = j :=
      funext fun k => Fin.append_right y₂ j k
    rw [hy1, hy2, hj1, hj2, mul_assoc]
  simp_rw [heq, ← Finset.mul_sum, hsum, mul_one]

/-! ### Block B: Part 1 (`b = 0`) and Part 2 (`G = 0`) -/

private theorem s3_dataChannelRef_zero_anc {S₁ S₂ : Set Gate} {n : ℕ}
    (A' : AdaptiveCircuit S₁ (n + 0)) (A : AdaptiveCircuit S₂ n)
    (hkraus : A'.krausList = A.krausList) (m_ref : ℕ)
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    A'.dataChannelRef m_ref ρ = A.channelRef m_ref ρ := by
  dsimp only [AdaptiveCircuit.dataChannelRef, AdaptiveCircuit.channelRef]
  rw [Finset.sum_eq_single (fun _ : Fin 0 => false)
    (fun j _ hj => False.elim (hj (funext fun i => Fin.elim0 i)))
    (fun h => False.elim (h (Finset.mem_univ _)))]
  have hcomp : ∀ K : Matrix (Qubits (n + 0)) (Qubits (n + 0)) ℂ,
      AdaptiveCircuit.ancillaCompress K (fun _ => false) = K := by
    intro K
    ext x y
    simp only [AdaptiveCircuit.ancillaCompress, Matrix.of_apply]
    have hx : Fin.append x (fun _ : Fin 0 => false) = x := by
      funext i
      have hi : i = Fin.castAdd 0 ⟨i.1, i.2⟩ := rfl
      rw [hi, Fin.append_left]
      rfl
    have hy : Fin.append y (fun _ : Fin 0 => false) = y := by
      funext i
      have hi : i = Fin.castAdd 0 ⟨i.1, i.2⟩ := rfl
      rw [hi, Fin.append_left]
      rfl
    rw [hx, hy]
  simp_rw [hcomp]
  rw [hkraus]
  rfl

private noncomputable def s3_trans0 {n r : ℕ} :
    AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ (0 : ℕ)) ^ r)) n →
      AdaptiveCircuit CliffordT (n + 0)
  | .done => .done
  | .measure q next => .measure q (fun out => s3_trans0 (next out))
  | .gate g next =>
      letI := Classical.propDecidable
      if hg : g.gate ∈ CliffordT then
        .gate ⟨g.gate, hg, g.wires⟩ (s3_trans0 next)
      else
        s3_trans0 next

private theorem s3_trans0_maxGates {n r : ℕ}
    (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ (0 : ℕ)) ^ r)) n) :
    (s3_trans0 A).maxGates ≤ A.maxGates := by
  induction A with
  | done => simp [s3_trans0, AdaptiveCircuit.maxGates]
  | measure q next ih =>
      simp only [s3_trans0, AdaptiveCircuit.maxGates]
      exact max_le (le_trans (ih false) (le_max_left _ _))
        (le_trans (ih true) (le_max_right _ _))
  | gate g next ih =>
      dsimp only [s3_trans0, AdaptiveCircuit.maxGates]
      split_ifs
      · simp only [AdaptiveCircuit.maxGates]; omega
      · exact le_trans ih (Nat.le_add_left _ _)

private theorem s3_trans0_krausList (s2 : Thm9Step2API) {n r : ℕ}
    (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ (0 : ℕ)) ^ r)) n) :
    (s3_trans0 A).krausList = A.krausList := by
  induction A with
  | done => rfl
  | measure q next ih =>
      simp only [s3_trans0, AdaptiveCircuit.krausList, ih false, ih true]
      rfl
  | gate g next ih =>
      dsimp only [s3_trans0]
      split_ifs with hg
      · simp only [AdaptiveCircuit.krausList, ih]
        rfl
      · have hgrid : g.gate ∈ gridGates ((2 ^ (0 : ℕ)) ^ r) := by
          rcases g.mem with h | h
          · exact False.elim (hg h)
          · exact h
        rcases hgrid with ⟨j, hj, hgeq⟩
        have hj1 : j < 1 := by simpa using hj
        have hj0 : j = 0 := Nat.lt_one_iff.mp hj1
        subst hj0
        have hrot0 : g.gate = Gate.ofMatrix1 (rot 0) := by
          simpa using hgeq
        let har : g.gate.arity = 1 := congrArg Gate.arity hrot0
        let q : Fin n := g.wires (Fin.cast har.symm 0)
        let w1 : Fin 1 ↪ Fin n := ⟨fun _ => q, fun i₁ i₂ _ => Subsingleton.elim i₁ i₂⟩
        have hmat : embedOp g.gate.mat g.wires = t9_rotOnWire 0 q := by
          rw [s3_embedOp_of_gate_eq hrot0 g.wires w1 (fun i => by rw [Fin.eq_zero i]; rfl)]
          rfl
        simp only [AdaptiveCircuit.krausList, hmat, s2.rotOnWire_zero, Matrix.mul_one, List.map_id', ih]

private theorem s3_step3_b0 (s1 : Thm9Step1API) (s2 : Thm9Step2API) :
    ∀ (r : ℕ), 2 ≤ r → ∀ (ε : ℝ), 0 < ε → ∀ (n G : ℕ)
      (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ (0 : ℕ)) ^ r)) n),
      A.maxGates ≤ G →
      ∃ (a : ℕ) (A' : AdaptiveCircuit CliffordT (n + a)),
        (A'.maxGates : ℝ) ≤ (G : ℝ) ∧
        DiamondClose A'.dataChannelRef A.channelRef ε := by
  intro r _ ε hε n G A hAG
  refine ⟨0, s3_trans0 A, ?_, ?_⟩
  · exact_mod_cast le_trans (s3_trans0_maxGates A) hAG
  · intro m ρ _
    rw [s3_dataChannelRef_zero_anc (s3_trans0 A) A (s3_trans0_krausList s2 A) m ρ,
      s1.traceDist_self]
    exact le_of_lt hε

private def s3_transZeroGates {S : Set Gate} {n : ℕ} :
    (A : AdaptiveCircuit S n) → A.maxGates ≤ 0 → AdaptiveCircuit CliffordT (n + 0)
  | .done, _ => .done
  | .gate _ _, h => False.elim (by simp [AdaptiveCircuit.maxGates] at h)
  | .measure q next, h =>
      .measure q (fun out =>
        s3_transZeroGates (next out) (by
          simp only [AdaptiveCircuit.maxGates] at h
          cases out
          · exact le_trans (le_max_left _ _) h
          · exact le_trans (le_max_right _ _) h))

private theorem s3_transZeroGates_maxGates {S : Set Gate} {n : ℕ}
    (A : AdaptiveCircuit S n) (h : A.maxGates ≤ 0) :
    (s3_transZeroGates A h).maxGates = 0 := by
  induction A with
  | done => rfl
  | gate _ _ => simp [AdaptiveCircuit.maxGates] at h
  | measure q next ih =>
      simp only [s3_transZeroGates, AdaptiveCircuit.maxGates, ih false, ih true, max_self]

private theorem s3_transZeroGates_krausList {S : Set Gate} {n : ℕ}
    (A : AdaptiveCircuit S n) (h : A.maxGates ≤ 0) :
    (s3_transZeroGates A h).krausList = A.krausList := by
  induction A with
  | done => rfl
  | gate _ _ => simp [AdaptiveCircuit.maxGates] at h
  | measure q next ih =>
      simp only [s3_transZeroGates, AdaptiveCircuit.krausList, ih false, ih true]
      rfl

private theorem s3_step3_G0 (s1 : Thm9Step1API) :
    ∀ (r b : ℕ) (ε : ℝ), 0 < ε → ∀ (n : ℕ)
      (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n),
      A.maxGates ≤ 0 →
      ∃ (a : ℕ) (A' : AdaptiveCircuit CliffordT (n + a)),
        (A'.maxGates : ℝ) ≤ 0 ∧
        DiamondClose A'.dataChannelRef A.channelRef ε := by
  intro r b ε hε n A hA0
  refine ⟨0, s3_transZeroGates A hA0, ?_, ?_⟩
  · rw [s3_transZeroGates_maxGates]; norm_num
  · intro m ρ _
    rw [s3_dataChannelRef_zero_anc _ A (s3_transZeroGates_krausList A hA0) m ρ,
      s1.traceDist_self]
    exact le_of_lt hε

/-! ### Block C: Ancilla layout, angles, and base-B decomposition -/

private abbrev s3_B (b : ℕ) : ℕ := 2 ^ b
private abbrev s3_M (b r : ℕ) : ℕ := b * r
private abbrev s3_S (r b : ℕ) : ℕ := s3_B b * s3_M b r
private abbrev s3_L (r b : ℕ) : ℕ := 2 * s3_S r b
private abbrev s3_N (n r b : ℕ) : ℕ := n + (s3_L r b + s3_M b r)

private theorem s3_B_pos (b : ℕ) : 0 < s3_B b := Nat.pow_pos (by norm_num)

private theorem s3_M_pos {b r : ℕ} (hb : 1 ≤ b) (hr : 2 ≤ r) : 0 < s3_M b r :=
  Nat.mul_pos hb (by omega)

private theorem s3_S_pos {b r : ℕ} (hb : 1 ≤ b) (hr : 2 ≤ r) : 0 < s3_S r b :=
  Nat.mul_pos (s3_B_pos b) (s3_M_pos hb hr)

private def s3_slotOf (r b k s : ℕ) (hk : k < s3_B b) (hs : s < s3_M b r) : Fin (s3_S r b) :=
  ⟨s * s3_B b + k, by
    have h1 : s * s3_B b + k < (s + 1) * s3_B b := by rw [add_mul, one_mul]; omega
    exact lt_of_lt_of_le h1 (by rw [mul_comm]; exact Nat.mul_le_mul_left (s3_B b) hs)⟩

private def s3_slotK (r b : ℕ) (u : Fin (s3_S r b)) : ℕ := u.1 % s3_B b
private def s3_slotS (r b : ℕ) (u : Fin (s3_S r b)) : ℕ := u.1 / s3_B b

private theorem s3_slotK_lt (r b : ℕ) (u : Fin (s3_S r b)) : s3_slotK r b u < s3_B b :=
  Nat.mod_lt _ (s3_B_pos b)

private theorem s3_slotS_lt (r b : ℕ) (u : Fin (s3_S r b)) : s3_slotS r b u < s3_M b r := by
  dsimp only [s3_slotS]
  rw [Nat.div_lt_iff_lt_mul (s3_B_pos b), mul_comm]
  exact u.2

private theorem s3_slotK_slotOf (r b k s : ℕ) (hk : k < s3_B b) (hs : s < s3_M b r) :
    s3_slotK r b (s3_slotOf r b k s hk hs) = k := by
  dsimp only [s3_slotK, s3_slotOf]
  rw [add_comm, mul_comm s (s3_B b), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

private theorem s3_slotS_slotOf (r b k s : ℕ) (hk : k < s3_B b) (hs : s < s3_M b r) :
    s3_slotS r b (s3_slotOf r b k s hk hs) = s := by
  dsimp only [s3_slotS, s3_slotOf]
  rw [add_comm, mul_comm s (s3_B b), Nat.add_mul_div_left _ _ (s3_B_pos b),
    Nat.div_eq_of_lt hk, zero_add]

private theorem s3_slot_ext {r b : ℕ} {u v : Fin (s3_S r b)}
    (hk : s3_slotK r b u = s3_slotK r b v) (hs : s3_slotS r b u = s3_slotS r b v) :
    u = v := by
  dsimp only [s3_slotK, s3_slotS] at hk hs
  ext
  have hu := Nat.div_add_mod u.1 (s3_B b)
  have hv := Nat.div_add_mod v.1 (s3_B b)
  rw [← hu, ← hv, hs, hk]

private def s3_catIdx {r b : ℕ} (u : Fin (s3_S r b)) : Fin (s3_L r b) :=
  ⟨u.1, by have := u.2; dsimp only [s3_L]; omega⟩
private def s3_bankIdx {r b : ℕ} (u : Fin (s3_S r b)) : Fin (s3_L r b) :=
  ⟨s3_S r b + u.1, by have := u.2; dsimp only [s3_L]; omega⟩

private def s3_dataWire (n r b : ℕ) (q : Fin n) : Fin (s3_N n r b) :=
  Fin.castAdd (s3_L r b + s3_M b r) q

private def s3_dataWireEmb (n r b : ℕ) : Fin n ↪ Fin (s3_N n r b) :=
  ⟨s3_dataWire n r b, Fin.castAdd_injective n (s3_L r b + s3_M b r)⟩

private def s3_catWire (n r b : ℕ) (u : Fin (s3_S r b)) : Fin (s3_N n r b) :=
  Fin.natAdd n (Fin.castAdd (s3_M b r) (s3_catIdx u))

private def s3_bankWire (n r b : ℕ) (u : Fin (s3_S r b)) : Fin (s3_N n r b) :=
  Fin.natAdd n (Fin.castAdd (s3_M b r) (s3_bankIdx u))

private def s3_scratchWire (n r b : ℕ) (t : Fin (s3_M b r)) : Fin (s3_N n r b) :=
  Fin.natAdd n (Fin.natAdd (s3_L r b) t)

private theorem s3_catWire_inj (n r b : ℕ) {u v : Fin (s3_S r b)} :
    s3_catWire n r b u = s3_catWire n r b v ↔ u = v := by
  simp [Fin.ext_iff, s3_catWire, s3_catIdx]

private theorem s3_bankWire_inj (n r b : ℕ) {u v : Fin (s3_S r b)} :
    s3_bankWire n r b u = s3_bankWire n r b v ↔ u = v := by
  simp [Fin.ext_iff, s3_bankWire, s3_bankIdx]

private theorem s3_scratchWire_inj (n r b : ℕ) {t₁ t₂ : Fin (s3_M b r)} :
    s3_scratchWire n r b t₁ = s3_scratchWire n r b t₂ ↔ t₁ = t₂ := by
  simp [Fin.ext_iff, s3_scratchWire]

private theorem s3_catWire_ne_bankWire (n r b : ℕ) (u v : Fin (s3_S r b)) :
    s3_catWire n r b u ≠ s3_bankWire n r b v := by
  have hu := u.2
  simp [Fin.ext_iff, s3_catWire, s3_bankWire, s3_catIdx, s3_bankIdx]
  omega

private theorem s3_catWire_ne_scratchWire (n r b : ℕ) (u : Fin (s3_S r b)) (t : Fin (s3_M b r)) :
    s3_catWire n r b u ≠ s3_scratchWire n r b t := by
  have hu := u.2
  simp [Fin.ext_iff, s3_catWire, s3_scratchWire, s3_catIdx, s3_L]
  omega

private theorem s3_bankWire_ne_scratchWire (n r b : ℕ) (u : Fin (s3_S r b)) (t : Fin (s3_M b r)) :
    s3_bankWire n r b u ≠ s3_scratchWire n r b t := by
  have hu := u.2
  simp [Fin.ext_iff, s3_bankWire, s3_scratchWire, s3_bankIdx, s3_L]
  omega

private theorem s3_dataWire_ne_catWire (n r b : ℕ) (q : Fin n) (u : Fin (s3_S r b)) :
    s3_dataWire n r b q ≠ s3_catWire n r b u := by
  simp [Fin.ext_iff, s3_dataWire, s3_catWire, s3_catIdx]
  omega

private theorem s3_dataWire_ne_bankWire (n r b : ℕ) (q : Fin n) (u : Fin (s3_S r b)) :
    s3_dataWire n r b q ≠ s3_bankWire n r b u := by
  simp [Fin.ext_iff, s3_dataWire, s3_bankWire, s3_bankIdx]
  omega

private theorem s3_dataWire_ne_scratchWire (n r b : ℕ) (q : Fin n) (t : Fin (s3_M b r)) :
    s3_dataWire n r b q ≠ s3_scratchWire n r b t := by
  simp [Fin.ext_iff, s3_dataWire, s3_scratchWire]
  omega

private noncomputable def s3_θks (k s : ℕ) : ℝ :=
  2 * Real.pi * (k : ℝ) / (2 : ℝ) ^ (s + 1)

private noncomputable def s3_θslot (r b : ℕ) (u : Fin (s3_S r b)) : ℝ :=
  s3_θks (s3_slotK r b u) (s3_slotS r b u)

private theorem s3_θslot_slotOf (r b k s : ℕ) (hk : k < s3_B b) (hs : s < s3_M b r) :
    s3_θslot r b (s3_slotOf r b k s hk hs) = s3_θks k s := by
  dsimp only [s3_θslot]
  rw [s3_slotK_slotOf, s3_slotS_slotOf]

private noncomputable def s3_α (r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) (i : Fin (s3_L r b)) : ℝ :=
  s3_θslot r b ⟨i.1 % s3_S r b, Nat.mod_lt _ (s3_S_pos hb hr)⟩

private theorem s3_α_catIdx (r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) (u : Fin (s3_S r b)) :
    s3_α r b hb hr (s3_catIdx u) = s3_θslot r b u := by
  dsimp only [s3_α, s3_catIdx]
  congr 1
  ext
  exact Nat.mod_eq_of_lt u.2

private theorem s3_α_bankIdx (r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) (u : Fin (s3_S r b)) :
    s3_α r b hb hr (s3_bankIdx u) = s3_θslot r b u := by
  dsimp only [s3_α, s3_bankIdx]
  congr 1
  ext
  simp [Nat.add_mod_left, Nat.mod_eq_of_lt u.2]

private theorem s3_two_mul_θks_zero (k : ℕ) :
    2 * s3_θks k 0 = 2 * Real.pi * (k : ℝ) := by
  simp only [s3_θks, zero_add, pow_one]
  ring

private theorem s3_rotOnWire_two_θks_zero (s2 : Thm9Step2API) {N : ℕ} (k : ℕ) (q : Fin N) :
    t9_rotOnWire (2 * s3_θks k 0) q = 1 := by
  rw [s3_two_mul_θks_zero, s2.rotOnWire_two_pi_nat]

private theorem s3_rotOnWire_neg_θks_zero (s2 : Thm9Step2API) {N : ℕ} (k : ℕ) (q : Fin N) :
    t9_rotOnWire (-s3_θks k 0) q = t9_rotOnWire (s3_θks k 0) q := by
  rw [← one_mul (t9_rotOnWire (-s3_θks k 0) q), ← s3_rotOnWire_two_θks_zero s2 k q,
    ← s2.rotOnWire_add, show 2 * s3_θks k 0 + -s3_θks k 0 = s3_θks k 0 by ring]

private theorem s3_two_mul_θks_succ (k s' : ℕ) :
    2 * s3_θks k (s' + 1) = s3_θks k s' := by
  simp only [s3_θks, pow_succ]
  ring

private theorem s3_rotOnWire_succ_mul_neg (s2 : Thm9Step2API) {N : ℕ}
    (k s' : ℕ) (q : Fin N) :
    t9_rotOnWire (s3_θks k s') q * t9_rotOnWire (-s3_θks k (s' + 1)) q =
      t9_rotOnWire (s3_θks k (s' + 1)) q := by
  rw [← s2.rotOnWire_add, ← s3_two_mul_θks_succ k s',
    show 2 * s3_θks k (s' + 1) + -s3_θks k (s' + 1) = s3_θks k (s' + 1) by ring]

private def s3_digit (B j ℓ : ℕ) : ℕ := (j / B ^ ℓ) % B

private theorem s3_digit_lt (B j ℓ : ℕ) (hB : 0 < B) : s3_digit B j ℓ < B :=
  Nat.mod_lt _ hB

private theorem s3_base_decomp (B : ℕ) (hB : 0 < B) :
    ∀ (r j : ℕ), j < B ^ r → j = ∑ ℓ : Fin r, s3_digit B j ℓ.1 * B ^ ℓ.1
  | 0, j, hj => by
      simp only [pow_zero, Nat.lt_one_iff] at hj
      subst hj
      simp
  | r + 1, j, hj => by
      rw [Fin.sum_univ_succ]
      have h0 : s3_digit B j (0 : Fin (r + 1)).1 * B ^ (0 : Fin (r + 1)).1 = j % B := by
        simp [s3_digit]
      have htail :
          (∑ ℓ : Fin r, s3_digit B j ℓ.succ.1 * B ^ ℓ.succ.1) =
          (∑ ℓ : Fin r, s3_digit B (j / B) ℓ.1 * B ^ ℓ.1) * B := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        have hdiv : j / (B * B ^ ℓ.1) = (j / B) / B ^ ℓ.1 := by
          rw [Nat.div_div_eq_div_mul]
        simp only [Fin.val_succ, s3_digit, pow_succ', hdiv]
        ring
      have hq : j / B < B ^ r := by
        rw [Nat.div_lt_iff_lt_mul hB]
        simpa [pow_succ] using hj
      rw [h0, htail, ← s3_base_decomp B hB r (j / B) hq]
      exact (Nat.mod_add_div' j B).symm

private def s3_levelOf (b r : ℕ) (ℓ : Fin r) : ℕ := b * (r - ℓ.1) - 1

private theorem s3_levelOf_lt (b r : ℕ) (hb : 1 ≤ b) (ℓ : Fin r) :
    s3_levelOf b r ℓ < s3_M b r := by
  dsimp only [s3_levelOf, s3_M]
  have h1 : 1 ≤ b * (r - ℓ.1) := Nat.mul_pos hb (Nat.sub_pos_of_lt ℓ.2)
  have h2 : b * (r - ℓ.1) ≤ b * r := Nat.mul_le_mul_left b (Nat.sub_le r ℓ.1)
  omega

private theorem s3_grid_angle_eq_sum (b r : ℕ) (hb : 1 ≤ b) (j : ℕ)
    (hj : j < (s3_B b) ^ r) :
    2 * Real.pi * (j : ℝ) / (((s3_B b) ^ r : ℕ) : ℝ) =
      ∑ ℓ : Fin r, s3_θks (s3_digit (s3_B b) j ℓ.1) (s3_levelOf b r ℓ) := by
  have hj_eq := s3_base_decomp (s3_B b) (s3_B_pos b) r j hj
  conv_lhs => rw [hj_eq]
  push_cast
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  dsimp only [s3_θks, s3_levelOf]
  have hpos : 1 ≤ b * (r - ℓ.1) := Nat.mul_pos hb (Nat.sub_pos_of_lt ℓ.2)
  have hsub : b * (r - ℓ.1) - 1 + 1 = b * (r - ℓ.1) := Nat.sub_add_cancel hpos
  rw [hsub]
  have hpow : (2 : ℝ) ^ (b * (r - ℓ.1)) = ((2 : ℝ) ^ b) ^ (r - ℓ.1) := by
    rw [pow_mul]
  have hsplit : ((2 : ℝ) ^ b) ^ r = ((2 : ℝ) ^ b) ^ ℓ.1 * ((2 : ℝ) ^ b) ^ (r - ℓ.1) := by
    rw [← pow_add, Nat.add_sub_of_le ℓ.2.le]
  have hne : ((2 : ℝ) ^ b) ^ (r - ℓ.1) ≠ 0 := by positivity
  have hneℓ : ((2 : ℝ) ^ b) ^ ℓ.1 ≠ 0 := by positivity
  rw [hpow, hsplit]
  field_simp

/-! ### Block D: Bank state, syncBankLe, compileRot, potential & Pascal bounds -/

private abbrev s3_Bank (r b : ℕ) : Type := Fin (s3_S r b) → Bool

private noncomputable def s3_bankVec (r b : ℕ) (bank : s3_Bank r b) (v : Fin (s3_S r b)) :
    Bool → ℂ :=
  if bank v then resourceVec (s3_θslot r b v) else plusVec

private theorem s3_norm_sq_bankVec (s2 : Thm9Step2API) (r b : ℕ)
    (bank : s3_Bank r b) (v : Fin (s3_S r b)) :
    ‖s3_bankVec r b bank v false‖ ^ 2 + ‖s3_bankVec r b bank v true‖ ^ 2 = 1 := by
  dsimp only [s3_bankVec]
  split_ifs
  · exact s2.norm_sq_resourceVec _
  · exact s2.norm_sq_plusVec

private def s3_emptyCount {r b : ℕ} (bank : s3_Bank r b) : ℕ :=
  (Finset.univ.filter fun u : Fin (s3_S r b) => !bank u).card

private def s3_pot {r b : ℕ} (f : ℕ) (bank : s3_Bank r b) : ℕ :=
  2 * f + s3_emptyCount bank

private theorem s3_emptyCount_update_false {r b : ℕ} (bank : s3_Bank r b)
    (u : Fin (s3_S r b)) (hu : bank u = true) :
    s3_emptyCount (Function.update bank u false) = s3_emptyCount bank + 1 := by
  dsimp only [s3_emptyCount]
  have hset :
      Finset.univ.filter (fun v : Fin (s3_S r b) => !Function.update bank u false v) =
      insert u (Finset.univ.filter fun v : Fin (s3_S r b) => !bank v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hv : v = u
    · subst hv; simp [hu]
    · simp [hv]
  have hnot : u ∉ Finset.univ.filter (fun v : Fin (s3_S r b) => !bank v) := by
    simp [hu]
  rw [hset, Finset.card_insert_of_notMem hnot]

private theorem s3_emptyCount_update_true {r b : ℕ} (bank : s3_Bank r b)
    (u : Fin (s3_S r b)) (hu : bank u = false) :
    s3_emptyCount (Function.update bank u true) + 1 = s3_emptyCount bank := by
  dsimp only [s3_emptyCount]
  have hset :
      Finset.univ.filter (fun v : Fin (s3_S r b) => !bank v) =
      insert u (Finset.univ.filter fun v : Fin (s3_S r b) => !Function.update bank u true v) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hv : v = u
    · subst hv; simp [hu]
    · simp [hv]
  have hnot :
      u ∉ Finset.univ.filter (fun v : Fin (s3_S r b) => !Function.update bank u true v) := by
    simp
  rw [hset, Finset.card_insert_of_notMem hnot]

private def s3_ValidTarget (n r b s : ℕ) (target : Fin (s3_N n r b)) : Prop :=
  target.1 < n ∨ n + s3_L r b + s < target.1

private theorem s3_ValidTarget_dataWire (n r b s : ℕ) (q : Fin n) :
    s3_ValidTarget n r b s (s3_dataWire n r b q) :=
  Or.inl q.2

private theorem s3_ValidTarget_pred {n r b s' : ℕ} {target : Fin (s3_N n r b)}
    (h : s3_ValidTarget n r b (s' + 1) target) :
    s3_ValidTarget n r b s' target := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

private theorem s3_ValidTarget_scratch (n r b s' : ℕ) (hs : s' + 1 < s3_M b r) :
    s3_ValidTarget n r b s' (s3_scratchWire n r b ⟨s' + 1, hs⟩) := by
  right
  simp only [s3_scratchWire, Fin.val_natAdd]
  omega

private theorem s3_targ_ne_bank (n r b s : ℕ) (target : Fin (s3_N n r b))
    (u : Fin (s3_S r b)) (ht : s3_ValidTarget n r b s target) :
    target ≠ s3_bankWire n r b u := by
  intro heq
  have hu := u.2
  have hval := congrArg Fin.val heq
  simp only [s3_bankWire, Fin.val_natAdd, Fin.val_castAdd, s3_bankIdx] at hval
  rcases ht with ht | ht
  · omega
  · dsimp only [s3_L] at ht; omega

private theorem s3_targ_ne_cat (n r b s : ℕ) (target : Fin (s3_N n r b))
    (u : Fin (s3_S r b)) (ht : s3_ValidTarget n r b s target) :
    target ≠ s3_catWire n r b u := by
  intro heq
  have hu := u.2
  have hval := congrArg Fin.val heq
  simp only [s3_catWire, Fin.val_natAdd, Fin.val_castAdd, s3_catIdx] at hval
  rcases ht with ht | ht
  · omega
  · dsimp only [s3_L] at ht; omega

private theorem s3_targ_ne_scratch (n r b s : ℕ) (target : Fin (s3_N n r b))
    (t : Fin (s3_M b r)) (hts : t.1 ≤ s) (ht : s3_ValidTarget n r b s target) :
    target ≠ s3_scratchWire n r b t := by
  intro heq
  have hval := congrArg Fin.val heq
  simp only [s3_scratchWire, Fin.val_natAdd] at hval
  rcases ht with ht | ht <;> omega

private def s3_w1 {N : ℕ} (q : Fin N) : Fin 1 ↪ Fin N :=
  ⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩

private def s3_w4 (n r b : ℕ) (_hb : 1 ≤ b) (_hr : 2 ≤ r)
    (k : ℕ) (hk : k < s3_B b) (s : ℕ) (hs : s < s3_M b r)
    (target : Fin (s3_N n r b)) (htarg : s3_ValidTarget n r b s target) :
    Fin 4 ↪ Fin (s3_N n r b) :=
  let u := s3_slotOf r b k s hk hs
  ⟨![s3_catWire n r b u, target, s3_bankWire n r b u, s3_scratchWire n r b ⟨s, hs⟩], by
    intro i j hij
    have h01 : s3_catWire n r b u ≠ target := (s3_targ_ne_cat n r b s target u htarg).symm
    have h02 : s3_catWire n r b u ≠ s3_bankWire n r b u := s3_catWire_ne_bankWire n r b u u
    have h03 : s3_catWire n r b u ≠ s3_scratchWire n r b ⟨s, hs⟩ :=
      s3_catWire_ne_scratchWire n r b u ⟨s, hs⟩
    have h12 : target ≠ s3_bankWire n r b u := s3_targ_ne_bank n r b s target u htarg
    have h13 : target ≠ s3_scratchWire n r b ⟨s, hs⟩ :=
      s3_targ_ne_scratch n r b s target ⟨s, hs⟩ le_rfl htarg
    have h23 : s3_bankWire n r b u ≠ s3_scratchWire n r b ⟨s, hs⟩ :=
      s3_bankWire_ne_scratchWire n r b u ⟨s, hs⟩
    fin_cases i <;> fin_cases j <;> (try rfl)
    · exact False.elim (h01 hij)
    · exact False.elim (h02 hij)
    · exact False.elim (h03 hij)
    · exact False.elim (h01 hij.symm)
    · exact False.elim (h12 hij)
    · exact False.elim (h13 hij)
    · exact False.elim (h02 hij.symm)
    · exact False.elim (h12 hij.symm)
    · exact False.elim (h23 hij)
    · exact False.elim (h03 hij.symm)
    · exact False.elim (h13 hij.symm)
    · exact False.elim (h23 hij.symm)⟩

private def s3_HasAncStateLe (n r b s_bound : ℕ) (bank : s3_Bank r b) {m_ref : ℕ}
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) : Prop :=
  (∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s_bound →
    t9_HasPureWire (s3_catWire n r b v) (resourceVec (s3_θslot r b v)) σ) ∧
  (∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s_bound →
    t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank v) σ) ∧
  (∀ t : Fin (s3_M b r), t.1 ≤ s_bound →
    t9_HasPureWire (s3_scratchWire n r b t) (basisVec false) σ)

private theorem s3_HasAncStateLe_mono {n r b s₁ s₂ : ℕ} (hs : s₁ ≤ s₂)
    {bank : s3_Bank r b} {m_ref : ℕ}
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (h : s3_HasAncStateLe n r b s₂ bank σ) :
    s3_HasAncStateLe n r b s₁ bank σ :=
  ⟨fun v hv => h.1 v (le_trans hv hs),
   fun v hv => h.2.1 v (le_trans hv hs),
   fun t ht => h.2.2 t (le_trans ht hs)⟩

private theorem s3_HasAncStateLe_init (s2 : Thm9Step2API) (n r b : ℕ)
    (hb : 1 ≤ b) (hr : 2 ≤ r) {m_ref : ℕ}
    (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ) :
    s3_HasAncStateLe n r b (s3_M b r - 1) (fun _ => true)
      (t9_tensorAncVec (t9_productAncVec (s3_α r b hb hr)) ρ) := by
  refine ⟨fun v _ => ?_, fun v _ => ?_, fun t _ => ?_⟩
  · have h := s2.hasPureWire_productAncVec_left (M := s3_M b r) (s3_α r b hb hr) ρ (s3_catIdx v)
    rw [s3_α_catIdx] at h
    exact h
  · have h := s2.hasPureWire_productAncVec_left (M := s3_M b r) (s3_α r b hb hr) ρ (s3_bankIdx v)
    rw [s3_α_bankIdx] at h
    dsimp only [s3_bankVec]
    rw [if_pos rfl]
    exact h
  · exact s2.hasPureWire_productAncVec_right (s3_α r b hb hr) ρ t

private theorem s3_HasAncStateLe_unitConj_embedOp (s2 : Thm9Step2API)
    {k n r b s_bound m_ref : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin (s3_N n r b))
    (hw_cat : ∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s_bound → s3_catWire n r b v ∉ Set.range w)
    (hw_bank : ∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s_bound → s3_bankWire n r b v ∉ Set.range w)
    (hw_scr : ∀ t : Fin (s3_M b r), t.1 ≤ s_bound → s3_scratchWire n r b t ∉ Set.range w)
    {bank : s3_Bank r b}
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (h : s3_HasAncStateLe n r b s_bound bank σ) :
    s3_HasAncStateLe n r b s_bound bank (t9_unitConj (embedOp M w) σ) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun t ht => ?_⟩
  · dsimp only [t9_HasPureWire]
    rw [← s2.traceAndSetWire_unitConj_embedOp M w (hw_cat v hv), h.1 v hv]
  · dsimp only [t9_HasPureWire]
    rw [← s2.traceAndSetWire_unitConj_embedOp M w (hw_bank v hv), h.2.1 v hv]
  · dsimp only [t9_HasPureWire]
    rw [← s2.traceAndSetWire_unitConj_embedOp M w (hw_scr t ht), h.2.2 t ht]

private theorem s3_HasAncStateLe_unitConj_data (s2 : Thm9Step2API)
    {k n r b s_bound m_ref : ℕ}
    (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n)
    {bank : s3_Bank r b}
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (h : s3_HasAncStateLe n r b s_bound bank σ) :
    s3_HasAncStateLe n r b s_bound bank (t9_unitConj (embedOp M (w.trans (s3_dataWireEmb n r b))) σ) := by
  refine s3_HasAncStateLe_unitConj_embedOp s2 M (w.trans (s3_dataWireEmb n r b))
    (fun v _ => by rintro ⟨i, hi⟩; exact s3_dataWire_ne_catWire n r b (w i) v hi)
    (fun v _ => by rintro ⟨i, hi⟩; exact s3_dataWire_ne_bankWire n r b (w i) v hi)
    (fun t _ => by rintro ⟨i, hi⟩; exact s3_dataWire_ne_scratchWire n r b (w i) t hi) h

private theorem s3_HasAncStateLe_of_proj_smul (s2 : Thm9Step2API)
    {n r b s_bound m_ref : ℕ} (q : Fin n) (out : Bool) {p : ℝ} (hp : p ≠ 0)
    {bank : s3_Bank r b}
    {σ σ_out : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (h : s3_HasAncStateLe n r b s_bound bank σ)
    (heq : t9_unitConj (AdaptiveCircuit.proj (s3_dataWire n r b q) out) σ = (p : ℂ) • σ_out) :
    s3_HasAncStateLe n r b s_bound bank σ_out := by
  have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp
  have hcancel : ∀ q_anc : Fin (s3_N n r b), q_anc ≠ s3_dataWire n r b q →
      ∀ v : Bool → ℂ, t9_HasPureWire q_anc v σ → t9_HasPureWire q_anc v σ_out := by
    intro q_anc hne v hpure
    have h1 : (p : ℂ) • t9_traceAndSetWire q_anc v σ_out = (p : ℂ) • σ_out := by
      rw [← s3_t9_traceAndSetWire_smul, ← heq,
        ← s2.traceAndSetWire_unitConj_proj hne out v σ, hpure, heq]
    exact smul_right_injective _ hpc h1
  exact ⟨fun v hv => hcancel _ (s3_dataWire_ne_catWire n r b q v).symm _ (h.1 v hv),
    fun v hv => hcancel _ (s3_dataWire_ne_bankWire n r b q v).symm _ (h.2.1 v hv),
    fun t ht => hcancel _ (s3_dataWire_ne_scratchWire n r b q t).symm _ (h.2.2 t ht)⟩

private noncomputable def s3_syncLevel (n r b m_ref : ℕ) (bank' : s3_Bank r b)
    (s'' : ℕ) (hs'' : s'' < s3_M b r)
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) :
    Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ :=
  (List.finRange (s3_B b)).foldr
    (fun k'' acc =>
      let v := s3_slotOf r b k''.1 s'' k''.2 hs''
      t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc)
    σ

private noncomputable def s3_syncBankLe (n r b m_ref : ℕ) (bank' : s3_Bank r b) :
    (s : ℕ) → s < s3_M b r →
    Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ →
    Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ
  | 0, hs, σ => s3_syncLevel n r b m_ref bank' 0 hs σ
  | s' + 1, hs, σ =>
      s3_syncLevel n r b m_ref bank' (s' + 1) hs
        (s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ)

private theorem s3_syncLevel_comm_embedOp (s2 : Thm9Step2API)
    {k n r b m_ref : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin (s3_N n r b))
    (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    (hw : ∀ v : Fin (s3_S r b), s3_slotS r b v = s'' → s3_bankWire n r b v ∉ Set.range w)
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) :
    s3_syncLevel n r b m_ref bank' s'' hs'' (t9_unitConj (embedOp M w) σ) =
      t9_unitConj (embedOp M w) (s3_syncLevel n r b m_ref bank' s'' hs'' σ) := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))),
      l.foldr (fun k'' acc =>
        let v := s3_slotOf r b k''.1 s'' k''.2 hs''
        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc)
        (t9_unitConj (embedOp M w) σ) =
      t9_unitConj (embedOp M w)
        (l.foldr (fun k'' acc =>
          let v := s3_slotOf r b k''.1 s'' k''.2 hs''
          t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ) := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
        dsimp only [List.foldr_cons]
        rw [ih]
        let v := s3_slotOf r b a.1 s'' a.2 hs''
        have hv : s3_slotS r b v = s'' := s3_slotS_slotOf r b a.1 s'' a.2 hs''
        exact (s2.traceAndSetWire_unitConj_embedOp M w (hw v hv) _ _).symm
  exact hfold (List.finRange (s3_B b))

private theorem s3_syncBankLe_comm_embedOp (s2 : Thm9Step2API)
    {k n r b m_ref : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin (s3_N n r b))
    (bank' : s3_Bank r b) :
    ∀ (s : ℕ) (hs : s < s3_M b r),
      (∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s → s3_bankWire n r b v ∉ Set.range w) →
      ∀ (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
      s3_syncBankLe n r b m_ref bank' s hs (t9_unitConj (embedOp M w) σ) =
        t9_unitConj (embedOp M w) (s3_syncBankLe n r b m_ref bank' s hs σ)
  | 0, hs, hw, σ =>
      s3_syncLevel_comm_embedOp s2 M w bank' 0 hs (fun v hv => hw v (le_of_eq hv)) σ
  | s' + 1, hs, hw, σ => by
      dsimp only [s3_syncBankLe]
      rw [s3_syncBankLe_comm_embedOp s2 M w bank' s' (Nat.lt_of_succ_lt hs)
        (fun v hv => hw v (Nat.le_succ_of_le hv)) σ]
      exact s3_syncLevel_comm_embedOp s2 M w bank' (s' + 1) hs
        (fun v hv => hw v (le_of_eq hv)) _

private theorem s3_syncLevel_comm_wire (n r b m_ref : ℕ) {q : Fin (s3_N n r b)}
    (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    (hq : ∀ v : Fin (s3_S r b), s3_slotS r b v = s'' → q ≠ s3_bankWire n r b v)
    (uvec : Bool → ℂ)
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) :
    s3_syncLevel n r b m_ref bank' s'' hs'' (t9_traceAndSetWire q uvec σ) =
      t9_traceAndSetWire q uvec (s3_syncLevel n r b m_ref bank' s'' hs'' σ) := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))),
      l.foldr (fun k'' acc =>
        let v := s3_slotOf r b k''.1 s'' k''.2 hs''
        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc)
        (t9_traceAndSetWire q uvec σ) =
      t9_traceAndSetWire q uvec
        (l.foldr (fun k'' acc =>
          let v := s3_slotOf r b k''.1 s'' k''.2 hs''
          t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ) := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
        dsimp only [List.foldr_cons]
        rw [ih]
        let v := s3_slotOf r b a.1 s'' a.2 hs''
        have hv : s3_slotS r b v = s'' := s3_slotS_slotOf r b a.1 s'' a.2 hs''
        exact s3_t9_traceAndSetWire_comm (hq v hv).symm _ uvec _
  exact hfold (List.finRange (s3_B b))

private theorem s3_syncBankLe_comm_wire (n r b m_ref : ℕ) {q : Fin (s3_N n r b)}
    (bank' : s3_Bank r b) :
    ∀ (s : ℕ) (hs : s < s3_M b r),
      (∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s → q ≠ s3_bankWire n r b v) →
      ∀ (uvec : Bool → ℂ)
      (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
      s3_syncBankLe n r b m_ref bank' s hs (t9_traceAndSetWire q uvec σ) =
        t9_traceAndSetWire q uvec (s3_syncBankLe n r b m_ref bank' s hs σ)
  | 0, hs, hq, uvec, σ =>
      s3_syncLevel_comm_wire n r b m_ref bank' 0 hs (fun v hv => hq v (le_of_eq hv)) uvec σ
  | s' + 1, hs, hq, uvec, σ => by
      dsimp only [s3_syncBankLe]
      rw [s3_syncBankLe_comm_wire n r b m_ref bank' s' (Nat.lt_of_succ_lt hs)
        (fun v hv => hq v (Nat.le_succ_of_le hv)) uvec σ]
      exact s3_syncLevel_comm_wire n r b m_ref bank' (s' + 1) hs
        (fun v hv => hq v (le_of_eq hv)) uvec _

private theorem s3_syncLevel_preserves_other_pure (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    {q : Fin (s3_N n r b)} (hq : ∀ v : Fin (s3_S r b), s3_slotS r b v = s'' → q ≠ s3_bankWire n r b v)
    (uvec : Bool → ℂ)
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (hp : t9_HasPureWire q uvec σ) :
    t9_HasPureWire q uvec (s3_syncLevel n r b m_ref bank' s'' hs'' σ) := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))),
      t9_HasPureWire q uvec
        (l.foldr (fun k'' acc =>
          let v := s3_slotOf r b k''.1 s'' k''.2 hs''
          t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ) := by
    intro l
    induction l with
    | nil => exact hp
    | cons a as ih =>
        dsimp only [List.foldr_cons]
        let v := s3_slotOf r b a.1 s'' a.2 hs''
        have hv : s3_slotS r b v = s'' := s3_slotS_slotOf r b a.1 s'' a.2 hs''
        exact s2.hasPureWire_traceAndSet_other (hq v hv).symm _ _ ih
  exact hfold (List.finRange (s3_B b))

private theorem s3_syncBankLe_preserves_other_pure (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) {q : Fin (s3_N n r b)} :
    ∀ (s : ℕ) (hs : s < s3_M b r),
      (∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s → q ≠ s3_bankWire n r b v) →
      ∀ (uvec : Bool → ℂ)
      {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ},
      t9_HasPureWire q uvec σ →
      t9_HasPureWire q uvec (s3_syncBankLe n r b m_ref bank' s hs σ)
  | 0, hs, hq, uvec, σ, hp =>
      s3_syncLevel_preserves_other_pure s2 bank' 0 hs (fun v hv => hq v (le_of_eq hv)) uvec hp
  | s' + 1, hs, hq, uvec, σ, hp => by
      dsimp only [s3_syncBankLe]
      have ih := s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
        (fun v hv => hq v (Nat.le_succ_of_le hv)) uvec hp
      exact s3_syncLevel_preserves_other_pure s2 bank' (s' + 1) hs
        (fun v hv => hq v (le_of_eq hv)) uvec ih

private theorem s3_syncLevel_eq_single (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) (k : ℕ) (hk : k < s3_B b)
    (s'' : ℕ) (hs'' : s'' < s3_M b r)
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (hp : ∀ (k'' : Fin (s3_B b)), k'' ≠ ⟨k, hk⟩ →
      let v := s3_slotOf r b k''.1 s'' k''.2 hs''
      t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) σ) :
    s3_syncLevel n r b m_ref bank' s'' hs'' σ =
      let u := s3_slotOf r b k s'' hk hs''
      t9_traceAndSetWire (s3_bankWire n r b u) (s3_bankVec r b bank' u) σ := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))), l.Nodup →
      (∀ k'' ∈ l, k'' ≠ ⟨k, hk⟩ →
        t9_HasPureWire (s3_bankWire n r b (s3_slotOf r b k''.1 s'' k''.2 hs''))
          (s3_bankVec r b bank' (s3_slotOf r b k''.1 s'' k''.2 hs'')) σ) →
      l.foldr (fun k'' acc =>
        let v := s3_slotOf r b k''.1 s'' k''.2 hs''
        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ =
      if ⟨k, hk⟩ ∈ l then
        t9_traceAndSetWire (s3_bankWire n r b (s3_slotOf r b k s'' hk hs''))
          (s3_bankVec r b bank' (s3_slotOf r b k s'' hk hs'')) σ
      else σ := by
    intro l hnodup hmem
    induction l with
    | nil => simp
    | cons a as ih =>
        rw [List.nodup_cons] at hnodup
        have hih := ih hnodup.2 (fun k'' hk'' hne => hmem k'' (List.mem_cons_of_mem a hk'') hne)
        dsimp only [List.foldr_cons]
        rw [hih]
        by_cases ha : a = ⟨k, hk⟩
        · subst ha
          rw [if_neg hnodup.1, if_pos (List.mem_cons_self)]
        · by_cases hkas : ⟨k, hk⟩ ∈ as
          · have hmem_cons : ⟨k, hk⟩ ∈ a :: as := List.mem_cons_of_mem a hkas
            rw [if_pos hkas, if_pos hmem_cons]
            have hne_wire :
                s3_bankWire n r b (s3_slotOf r b k s'' hk hs'') ≠
                s3_bankWire n r b (s3_slotOf r b a.1 s'' a.2 hs'') := by
              intro h
              rw [s3_bankWire_inj] at h
              apply ha
              ext
              simpa [s3_slotK_slotOf] using (congrArg (s3_slotK r b) h).symm
            exact s2.hasPureWire_traceAndSet_other hne_wire _ _
              (hmem a List.mem_cons_self ha)
          · have hnot_cons : ⟨k, hk⟩ ∉ a :: as := by
              simp [List.mem_cons, Ne.symm ha, hkas]
            rw [if_neg hkas, if_neg hnot_cons]
            exact hmem a List.mem_cons_self ha
  rw [hfold (List.finRange (s3_B b)) (List.nodup_finRange _) (fun k'' _ hne => hp k'' hne),
    if_pos (List.mem_finRange _)]

private theorem s3_syncLevel_preserves_all_at_level (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) :
    ∀ v : Fin (s3_S r b), s3_slotS r b v = s'' →
      t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v)
        (s3_syncLevel n r b m_ref bank' s'' hs'' σ) := by
  intro v hv
  let kv : Fin (s3_B b) := ⟨s3_slotK r b v, s3_slotK_lt r b v⟩
  have hv_eq : s3_slotOf r b kv.1 s'' kv.2 hs'' = v := by
    apply s3_slot_ext
    · rw [s3_slotK_slotOf]
    · rw [s3_slotS_slotOf, hv]
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))), l.Nodup → kv ∈ l →
      t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v)
        (l.foldr (fun k'' acc =>
          let w := s3_slotOf r b k''.1 s'' k''.2 hs''
          t9_traceAndSetWire (s3_bankWire n r b w) (s3_bankVec r b bank' w) acc) σ) := by
    intro l hnodup hmem
    induction l with
    | nil => cases hmem
    | cons a as ih =>
        rw [List.nodup_cons] at hnodup
        dsimp only [List.foldr_cons]
        by_cases ha : a = kv
        · subst ha
          have hslot : s3_slotOf r b kv.1 s'' kv.2 hs'' = v := hv_eq
          rw [hslot]
          exact s2.hasPureWire_traceAndSet_self _ _ (s3_norm_sq_bankVec s2 r b bank' v) _
        · have hmem' : kv ∈ as := by
            simpa [List.mem_cons, Ne.symm ha] using hmem
          have ih' := ih hnodup.2 hmem'
          have hne_wire :
              s3_bankWire n r b (s3_slotOf r b a.1 s'' a.2 hs'') ≠ s3_bankWire n r b v := by
            intro h
            rw [s3_bankWire_inj] at h
            apply ha
            ext
            have := congrArg (s3_slotK r b) h
            rwa [s3_slotK_slotOf] at this
          exact s2.hasPureWire_traceAndSet_other hne_wire _ _ ih'
  exact hfold (List.finRange (s3_B b)) (List.nodup_finRange _) (List.mem_finRange _)

private theorem s3_syncBankLe_preserves_HasAncStateLe (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank bank' : s3_Bank r b) :
    ∀ (s : ℕ) (hs : s < s3_M b r),
      (∀ v : Fin (s3_S r b), s < s3_slotS r b v → bank' v = bank v) →
      ∀ {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ},
      s3_HasAncStateLe n r b (s3_M b r - 1) bank σ →
      s3_HasAncStateLe n r b (s3_M b r - 1) bank' (s3_syncBankLe n r b m_ref bank' s hs σ)
  | 0, hs, hagree, σ, hanc => by
      refine ⟨fun v hv => ?_, fun v hv => ?_, fun t ht => ?_⟩
      · exact s3_syncLevel_preserves_other_pure s2 bank' 0 hs
          (fun w _ => (s3_catWire_ne_bankWire n r b v w)) _ (hanc.1 v hv)
      · by_cases hvs : s3_slotS r b v = 0
        · exact s3_syncLevel_preserves_all_at_level s2 bank' 0 hs σ v hvs
        · have hpos : 0 < s3_slotS r b v := Nat.pos_of_ne_zero hvs
          have heqb : bank' v = bank v := hagree v hpos
          have hp : t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) σ := by
            simpa [s3_bankVec, heqb] using hanc.2.1 v hv
          exact s3_syncLevel_preserves_other_pure s2 bank' 0 hs
            (fun w hw => by
              intro h
              rw [s3_bankWire_inj] at h
              subst h
              exact hvs hw) _ hp
      · exact s3_syncLevel_preserves_other_pure s2 bank' 0 hs
          (fun w _ => (s3_bankWire_ne_scratchWire n r b w t).symm) _ (hanc.2.2 t ht)
  | s' + 1, hs, hagree, σ, hanc => by
      dsimp only [s3_syncBankLe]
      let bank_mid : s3_Bank r b := fun v => if s3_slotS r b v ≤ s' then bank' v else bank v
      have ih_mid :
          ∀ (w : Fin (s3_S r b)), s3_slotS r b w ≤ s' →
            t9_HasPureWire (s3_bankWire n r b w) (s3_bankVec r b bank' w)
              (s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ) := by
        have hstep1 :
            s3_HasAncStateLe n r b (s3_M b r - 1) bank_mid
              (s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ) := by
          have hsync_eq :
              s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ =
              s3_syncBankLe n r b m_ref bank_mid s' (Nat.lt_of_succ_lt hs) σ := by
            have hgen : ∀ (k_s : ℕ) (hk_s : k_s < s3_M b r), k_s ≤ s' →
                s3_syncBankLe n r b m_ref bank' k_s hk_s σ =
                s3_syncBankLe n r b m_ref bank_mid k_s hk_s σ := by
              intro k_s hk_s hle
              induction k_s with
              | zero =>
                  dsimp only [s3_syncBankLe, s3_syncLevel]
                  have hfc : ∀ (l : List (Fin (s3_B b))),
                      l.foldr (fun k'' acc =>
                        let v := s3_slotOf r b k''.1 0 k''.2 hk_s
                        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ =
                      l.foldr (fun k'' acc =>
                        let v := s3_slotOf r b k''.1 0 k''.2 hk_s
                        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank_mid v) acc) σ := by
                    intro l
                    induction l with
                    | nil => rfl
                    | cons a as iha =>
                        dsimp only [List.foldr_cons]
                        rw [iha]
                        have hbm : bank_mid (s3_slotOf r b a.1 0 a.2 hk_s) =
                            bank' (s3_slotOf r b a.1 0 a.2 hk_s) := by
                          simp [bank_mid, s3_slotS_slotOf]
                        simp [s3_bankVec, hbm]
                  exact hfc (List.finRange (s3_B b))
              | succ j ihj =>
                  dsimp only [s3_syncBankLe]
                  rw [ihj (Nat.lt_of_succ_lt hk_s) (Nat.le_of_succ_le hle)]
                  dsimp only [s3_syncLevel]
                  have hfc : ∀ (l : List (Fin (s3_B b)))
                      (τ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
                      l.foldr (fun k'' acc =>
                        let v := s3_slotOf r b k''.1 (j + 1) k''.2 hk_s
                        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) τ =
                      l.foldr (fun k'' acc =>
                        let v := s3_slotOf r b k''.1 (j + 1) k''.2 hk_s
                        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank_mid v) acc) τ := by
                    intro l τ
                    induction l with
                    | nil => rfl
                    | cons a as iha =>
                        dsimp only [List.foldr_cons]
                        rw [iha]
                        have hbm : bank_mid (s3_slotOf r b a.1 (j + 1) a.2 hk_s) =
                            bank' (s3_slotOf r b a.1 (j + 1) a.2 hk_s) := by
                          simp [bank_mid, s3_slotS_slotOf, hle]
                        simp [s3_bankVec, hbm]
                  exact hfc (List.finRange (s3_B b)) _
            exact hgen s' (Nat.lt_of_succ_lt hs) le_rfl
          rw [hsync_eq]
          exact s3_syncBankLe_preserves_HasAncStateLe s2 bank bank_mid s' (Nat.lt_of_succ_lt hs)
            (fun v hv => by simp [bank_mid, not_le.mpr hv]) hanc
        intro w hw
        have heqw : bank_mid w = bank' w := by simp [bank_mid, hw]
        have hw' : s3_slotS r b w ≤ s3_M b r - 1 := by
          have := s3_slotS_lt r b w; omega
        simpa [s3_bankVec, heqw] using hstep1.2.1 w hw'
      refine ⟨fun v hv => ?_, fun v hv => ?_, fun t ht => ?_⟩
      · exact s3_syncLevel_preserves_other_pure s2 bank' (s' + 1) hs
          (fun w _ => s3_catWire_ne_bankWire n r b v w) _
          (s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
            (fun w _ => s3_catWire_ne_bankWire n r b v w) _ (hanc.1 v hv))
      · by_cases hvs_eq : s3_slotS r b v = s' + 1
        · exact s3_syncLevel_preserves_all_at_level s2 bank' (s' + 1) hs _ v hvs_eq
        · by_cases hvs_le : s3_slotS r b v ≤ s'
          · exact s3_syncLevel_preserves_other_pure s2 bank' (s' + 1) hs
              (fun w hw => by
                intro h; rw [s3_bankWire_inj] at h; subst h; omega) _
              (ih_mid v hvs_le)
          · have hgt : s' + 1 < s3_slotS r b v := by omega
            have heqb : bank' v = bank v := hagree v hgt
            have hp : t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) σ := by
              simpa [s3_bankVec, heqb] using hanc.2.1 v hv
            exact s3_syncLevel_preserves_other_pure s2 bank' (s' + 1) hs
              (fun w hw => by
                intro h; rw [s3_bankWire_inj] at h; subst h; omega) _
              (s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
                (fun w hw => by
                  intro h; rw [s3_bankWire_inj] at h; subst h; omega) _ hp)
      · exact s3_syncLevel_preserves_other_pure s2 bank' (s' + 1) hs
          (fun w _ => (s3_bankWire_ne_scratchWire n r b w t).symm) _
          (s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
            (fun w _ => (s3_bankWire_ne_scratchWire n r b w t).symm) _ (hanc.2.2 t ht))

private theorem s3_syncLevel_partialTraceAnc (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ) :
    t9_partialTraceAnc (s3_syncLevel n r b m_ref bank' s'' hs'' σ) = t9_partialTraceAnc σ := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))),
      t9_partialTraceAnc (l.foldr (fun k'' acc =>
        let v := s3_slotOf r b k''.1 s'' k''.2 hs''
        t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ) =
      t9_partialTraceAnc σ := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih =>
        dsimp only [List.foldr_cons]
        let v := s3_slotOf r b a.1 s'' a.2 hs''
        change t9_partialTraceAnc
          (t9_traceAndSetWire (Fin.natAdd n (Fin.castAdd (s3_M b r) (s3_bankIdx v)))
            (s3_bankVec r b bank' v) _) = _
        rw [s2.partialTraceAnc_traceAndSetWire _ _ (s3_norm_sq_bankVec s2 r b bank' v), ih]
  exact hfold (List.finRange (s3_B b))

private theorem s3_syncBankLe_partialTraceAnc (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) :
    ∀ (s : ℕ) (hs : s < s3_M b r)
      (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
      t9_partialTraceAnc (s3_syncBankLe n r b m_ref bank' s hs σ) = t9_partialTraceAnc σ
  | 0, hs, σ => s3_syncLevel_partialTraceAnc s2 bank' 0 hs σ
  | s' + 1, hs, σ => by
      dsimp only [s3_syncBankLe]
      rw [s3_syncLevel_partialTraceAnc s2 bank' (s' + 1) hs,
        s3_syncBankLe_partialTraceAnc s2 bank' s' (Nat.lt_of_succ_lt hs) σ]

private theorem s3_syncLevel_isDensityOperator (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) (s'' : ℕ) (hs'' : s'' < s3_M b r)
    {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ}
    (hσ : WildeQIT.IsDensityOperator σ) :
    WildeQIT.IsDensityOperator (s3_syncLevel n r b m_ref bank' s'' hs'' σ) := by
  dsimp only [s3_syncLevel]
  have hfold : ∀ (l : List (Fin (s3_B b))),
      WildeQIT.IsDensityOperator
        (l.foldr (fun k'' acc =>
          let v := s3_slotOf r b k''.1 s'' k''.2 hs''
          t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ) := by
    intro l
    induction l with
    | nil => exact hσ
    | cons a as ih =>
        dsimp only [List.foldr_cons]
        exact s3_t9_traceAndSetWire_isDensityOperator _ _ (s3_norm_sq_bankVec s2 r b bank' _) ih
  exact hfold (List.finRange (s3_B b))

private theorem s3_syncBankLe_isDensityOperator (s2 : Thm9Step2API)
    {n r b m_ref : ℕ} (bank' : s3_Bank r b) :
    ∀ (s : ℕ) (hs : s < s3_M b r)
      {σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ},
      WildeQIT.IsDensityOperator σ →
      WildeQIT.IsDensityOperator (s3_syncBankLe n r b m_ref bank' s hs σ)
  | 0, hs, σ, hσ => s3_syncLevel_isDensityOperator s2 bank' 0 hs hσ
  | s' + 1, hs, σ, hσ => by
      dsimp only [s3_syncBankLe]
      exact s3_syncLevel_isDensityOperator s2 bank' (s' + 1) hs
        (s3_syncBankLe_isDensityOperator s2 bank' s' (Nat.lt_of_succ_lt hs) hσ)

private noncomputable def s3_compileRot
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r)
    (k : ℕ) (hk : k < s3_B b) :
    (s : ℕ) → (hs : s < s3_M b r) →
    (target : Fin (s3_N n r b)) → (htarg : s3_ValidTarget n r b s target) →
    ℕ → s3_Bank r b → (ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b)) →
    AdaptiveCircuit CliffordT (s3_N n r b)
  | 0, hs, target, htarg, iFuel, bank, cont =>
      let u := s3_slotOf r b k 0 hk hs
      if bank u then
        match iFuel with
        | 0 => .done
        | f + 1 =>
            let bank' := Function.update bank u false
            let hne := s3_targ_ne_bank n r b 0 target u htarg
            let w1 := s3_w1 (s3_bankWire n r b u)
            .gate (cnotApp t9_cnot_mem_cliffordT target (s3_bankWire n r b u) hne)
              (.measure (s3_bankWire n r b u) fun out =>
                match out with
                | false => t9_prependCircuit (s3_liftCircuit w1 resetFalse) (cont f bank')
                | true => t9_prependCircuit (s3_liftCircuit w1 resetTrue) (cont f bank'))
      else
        let bank_mid := Function.update bank u true
        let w4 := s3_w4 n r b hb hr k hk 0 hs target htarg
        t9_prependCircuit (s3_liftCircuit w4 half1)
          (t9_prependCircuit (s3_liftCircuit w4 half2) (cont iFuel bank_mid))
  | s' + 1, hs, target, htarg, iFuel, bank, cont =>
      let u := s3_slotOf r b k (s' + 1) hk hs
      if bank u then
        match iFuel with
        | 0 => .done
        | f + 1 =>
            let bank' := Function.update bank u false
            let hne := s3_targ_ne_bank n r b (s' + 1) target u htarg
            let w1 := s3_w1 (s3_bankWire n r b u)
            let hs' : s' < s3_M b r := Nat.lt_of_succ_lt hs
            let htarg' : s3_ValidTarget n r b s' target := s3_ValidTarget_pred htarg
            .gate (cnotApp t9_cnot_mem_cliffordT target (s3_bankWire n r b u) hne)
              (.measure (s3_bankWire n r b u) fun out =>
                match out with
                | false => t9_prependCircuit (s3_liftCircuit w1 resetFalse) (cont f bank')
                | true => t9_prependCircuit (s3_liftCircuit w1 resetTrue)
                    (s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s' hs'
                      target htarg' f bank' cont))
      else
        let bank_mid := Function.update bank u true
        let w4 := s3_w4 n r b hb hr k hk (s' + 1) hs target htarg
        let hs' : s' < s3_M b r := Nat.lt_of_succ_lt hs
        let htarg_s : s3_ValidTarget n r b s' (s3_scratchWire n r b ⟨s' + 1, hs⟩) :=
          s3_ValidTarget_scratch n r b s' hs
        t9_prependCircuit (s3_liftCircuit w4 half1)
          (s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s' hs'
            (s3_scratchWire n r b ⟨s' + 1, hs⟩) htarg_s iFuel bank_mid
            (fun iFuel' bank' => t9_prependCircuit (s3_liftCircuit w4 half2) (cont iFuel' bank')))

private theorem s3_compileRot_maxGates
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hrF : resetFalse.size ≤ 1) (hrT : resetTrue.size ≤ 5)
    (hh1 : half1.size ≤ 38) (hh2 : half2.size ≤ 36)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r)
    (k : ℕ) (hk : k < s3_B b) :
    ∀ (s : ℕ) (hs : s < s3_M b r)
      (target : Fin (s3_N n r b)) (htarg : s3_ValidTarget n r b s target)
      (iFuel : ℕ) (bank : s3_Bank r b)
      (cont : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b))
      (K_base : ℕ),
      (∀ f' b', (cont f' b').maxGates ≤ K_base + 74 * s3_pot f' b') →
      (s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s hs
        target htarg iFuel bank cont).maxGates ≤ K_base + 74 * s3_pot iFuel bank
  | 0, hs, target, htarg, iFuel, bank, cont, K_base, hcont => by
      dsimp only [s3_compileRot]
      by_cases hbank : bank (s3_slotOf r b k 0 hk hs) = true
      · rw [if_pos hbank]
        cases iFuel with
        | zero => simp [AdaptiveCircuit.maxGates]
        | succ f =>
            let u := s3_slotOf r b k 0 hk hs
            let bank' := Function.update bank u false
            have hpot : s3_pot f bank' + 1 = s3_pot (f + 1) bank := by
              dsimp only [s3_pot, bank']
              rw [s3_emptyCount_update_false bank u hbank]
              omega
            simp only [AdaptiveCircuit.maxGates, t9_prependCircuit_maxGates, s3_liftCircuit_size]
            have hf := hcont f bank'
            dsimp only [bank'] at hf hpot
            have hle_max :
                max (resetFalse.size + (cont f (Function.update bank u false)).maxGates)
                  (resetTrue.size + (cont f (Function.update bank u false)).maxGates) ≤
                K_base + 74 * s3_pot f (Function.update bank u false) + 5 :=
              max_le (by omega) (by omega)
            dsimp only [u] at hle_max hpot
            omega
      · have hbf : bank (s3_slotOf r b k 0 hk hs) = false := Bool.eq_false_iff.mpr hbank
        rw [if_neg hbank]
        let u := s3_slotOf r b k 0 hk hs
        let bank_mid := Function.update bank u true
        have hpot : s3_pot iFuel bank_mid + 1 = s3_pot iFuel bank := by
          dsimp only [s3_pot, bank_mid]
          have he := s3_emptyCount_update_true bank u hbf
          omega
        simp only [t9_prependCircuit_maxGates, s3_liftCircuit_size]
        have hm := hcont iFuel bank_mid
        dsimp only [bank_mid, u] at hm hpot
        omega
  | s' + 1, hs, target, htarg, iFuel, bank, cont, K_base, hcont => by
      dsimp only [s3_compileRot]
      by_cases hbank : bank (s3_slotOf r b k (s' + 1) hk hs) = true
      · rw [if_pos hbank]
        cases iFuel with
        | zero => simp [AdaptiveCircuit.maxGates]
        | succ f =>
            let u := s3_slotOf r b k (s' + 1) hk hs
            let bank' := Function.update bank u false
            have hpot : s3_pot f bank' + 1 = s3_pot (f + 1) bank := by
              dsimp only [s3_pot, bank']
              rw [s3_emptyCount_update_false bank u hbank]
              omega
            have ih := s3_compileRot_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
              n r b hb hr k hk s' (Nat.lt_of_succ_lt hs) target (s3_ValidTarget_pred htarg)
              f bank' cont K_base hcont
            simp only [AdaptiveCircuit.maxGates, t9_prependCircuit_maxGates, s3_liftCircuit_size]
            have hf := hcont f bank'
            have hmax : max (resetFalse.size + (cont f bank').maxGates)
                (resetTrue.size +
                  (s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s'
                    (Nat.lt_of_succ_lt hs) target (s3_ValidTarget_pred htarg)
                    f bank' cont).maxGates) ≤
                K_base + 74 * s3_pot f bank' + 5 := max_le (by omega) (by omega)
            dsimp only [bank', u] at hmax hpot
            omega
      · have hbf : bank (s3_slotOf r b k (s' + 1) hk hs) = false := Bool.eq_false_iff.mpr hbank
        rw [if_neg hbank]
        let u := s3_slotOf r b k (s' + 1) hk hs
        let bank_mid := Function.update bank u true
        let w4 := s3_w4 n r b hb hr k hk (s' + 1) hs target htarg
        have hpot : s3_pot iFuel bank_mid + 1 = s3_pot iFuel bank := by
          dsimp only [s3_pot, bank_mid]
          have he := s3_emptyCount_update_true bank u hbf
          omega
        let cont' : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b) :=
          fun iFuel' bank' => t9_prependCircuit (s3_liftCircuit w4 half2) (cont iFuel' bank')
        have hcont' : ∀ f' b', (cont' f' b').maxGates ≤ (K_base + 36) + 74 * s3_pot f' b' := by
          intro f' b'
          dsimp only [cont']
          rw [t9_prependCircuit_maxGates, s3_liftCircuit_size]
          have := hcont f' b'
          omega
        have ih := s3_compileRot_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
          n r b hb hr k hk s' (Nat.lt_of_succ_lt hs)
          (s3_scratchWire n r b ⟨s' + 1, hs⟩) (s3_ValidTarget_scratch n r b s' hs)
          iFuel bank_mid cont' (K_base + 36) hcont'
        rw [t9_prependCircuit_maxGates, s3_liftCircuit_size]
        dsimp only [cont', bank_mid, w4, u] at ih hpot
        omega

private noncomputable def s3_binomErr (f R : ℕ) : ℝ :=
  2 * ((∑ k ∈ Finset.range R, (f.choose k : ℝ)) / (2 : ℝ) ^ f)

private theorem s3_binomErr_nonneg (f R : ℕ) : 0 ≤ s3_binomErr f R := by
  dsimp only [s3_binomErr]
  positivity

private theorem s3_binomErr_mono_right (f : ℕ) {R₁ R₂ : ℕ} (hR : R₁ ≤ R₂) :
    s3_binomErr f R₁ ≤ s3_binomErr f R₂ := by
  dsimp only [s3_binomErr]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hR) (fun _ _ _ => by positivity)

private theorem s3_binomErr_zero_fuel (R : ℕ) : s3_binomErr 0 (R + 1) = 2 := by
  dsimp only [s3_binomErr]
  rw [Finset.sum_range_succ']
  have hzero : (∑ k ∈ Finset.range R, ((0 : ℕ).choose (k + 1) : ℝ)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Nat.choose_eq_zero_of_lt]
  rw [hzero, Nat.choose_zero_right]
  norm_num

private theorem s3_binomErr_pascal (f R : ℕ) :
    (1 / 2 : ℝ) * s3_binomErr f R + (1 / 2 : ℝ) * s3_binomErr f (R + 1) =
      s3_binomErr (f + 1) (R + 1) := by
  dsimp only [s3_binomErr]
  have hsplit :
      (∑ k ∈ Finset.range (R + 1), (f.choose k : ℝ)) =
      (f.choose 0 : ℝ) + ∑ k ∈ Finset.range R, (f.choose (k + 1) : ℝ) := by
    rw [Finset.sum_range_succ', add_comm]
  have hcomb :
      (∑ k ∈ Finset.range R, (f.choose k : ℝ)) +
        ∑ k ∈ Finset.range (R + 1), (f.choose k : ℝ) =
      ∑ k ∈ Finset.range (R + 1), ((f + 1).choose k : ℝ) := by
    rw [hsplit]
    have hsucc :
        (∑ k ∈ Finset.range R, (f.choose k : ℝ)) +
          ∑ k ∈ Finset.range R, (f.choose (k + 1) : ℝ) =
        ∑ k ∈ Finset.range R, ((f + 1).choose (k + 1) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact_mod_cast (Nat.choose_succ_succ f k).symm
    have h0 : (f.choose 0 : ℝ) = ((f + 1).choose 0 : ℝ) := by simp
    calc (∑ k ∈ Finset.range R, (f.choose k : ℝ)) +
          ((f.choose 0 : ℝ) + ∑ k ∈ Finset.range R, (f.choose (k + 1) : ℝ))
        = (f.choose 0 : ℝ) + ((∑ k ∈ Finset.range R, (f.choose k : ℝ)) +
            ∑ k ∈ Finset.range R, (f.choose (k + 1) : ℝ)) := by ring
      _ = ((f + 1).choose 0 : ℝ) + ∑ k ∈ Finset.range R, ((f + 1).choose (k + 1) : ℝ) := by
          rw [h0, hsucc]
      _ = ∑ k ∈ Finset.range (R + 1), ((f + 1).choose k : ℝ) := by
          rw [Finset.sum_range_succ', add_comm]
  have hpow : (2 : ℝ) ^ (f + 1) = 2 * (2 : ℝ) ^ f := by rw [pow_succ']
  rw [hpow, ← hcomb]
  ring

private theorem s3_compileRot_close (s1 : Thm9Step1API) (s2 : Thm9Step2API)
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hstep :
      ∀ (N m_ref : ℕ) (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire w_bank (resourceVec θ) σ →
        let w1_bank : Fin 1 ↪ Fin N := ⟨fun _ => w_bank, fun i j _ => Subsingleton.elim i j⟩
        let g_cnot := cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne
        let σ_cnot := t9_unitConj (embedOp g_cnot.gate.mat g_cnot.wires) σ
        let P (b : Bool) := AdaptiveCircuit.proj w_bank b
        t9_unitConj (embedOp resetFalse.unitary w1_bank) (t9_unitConj (P false) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire θ w_targ) (t9_traceAndSetWire w_bank plusVec σ) ∧
        t9_unitConj (embedOp resetTrue.unitary w1_bank) (t9_unitConj (P true) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire (-θ) w_targ) (t9_traceAndSetWire w_bank plusVec σ))
    (hsplit :
      ∀ (N m_ref : ℕ) (w : Fin 4 ↪ Fin N) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire (w 0) (resourceVec θ) σ →
        t9_HasPureWire (w 2) plusVec σ →
        t9_HasPureWire (w 3) (basisVec false) σ →
        t9_unitConj (embedOp half2.unitary w)
          (t9_unitConj (t9_rotOnWire (2 * θ) (w 3))
            (t9_unitConj (embedOp half1.unitary w) σ)) =
          t9_unitConj (t9_rotOnWire θ (w 1))
            (t9_traceAndSetWire (w 2) (resourceVec θ) σ))
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r)
    (k : ℕ) (hk : k < s3_B b) :
    ∀ (s : ℕ) (hs : s < s3_M b r)
      (target : Fin (s3_N n r b)) (htarg : s3_ValidTarget n r b s target)
      (iFuel : ℕ) (bank : s3_Bank r b)
      (cont : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b))
      (m_ref : ℕ)
      (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ)
      (target_mat : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ)
      (R : ℕ),
      WildeQIT.IsDensityOperator σ →
      s3_HasAncStateLe n r b s bank σ →
      WildeQIT.IsDensityOperator target_mat →
      (∀ (f' : ℕ), f' ≤ iFuel → ∀ (bank' : s3_Bank r b),
        (∀ v : Fin (s3_S r b), s < s3_slotS r b v → bank' v = bank v) →
        WildeQIT.traceDist
          (t9_partialTraceAnc ((cont f' bank').channelRef m_ref
            (t9_unitConj (t9_rotOnWire (s3_θks k s) target)
              (s3_syncBankLe n r b m_ref bank' s hs σ))))
          target_mat ≤ s3_binomErr f' R) →
      WildeQIT.traceDist
        (t9_partialTraceAnc
          ((s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s hs
            target htarg iFuel bank cont).channelRef m_ref σ))
        target_mat ≤ s3_binomErr iFuel (R + 1)
  | 0, hs, target, htarg, iFuel, bank, cont, m_ref, σ, target_mat, R, hσ, hanc, htarg_dens, hcont => by
      dsimp only [s3_compileRot]
      let u := s3_slotOf r b k 0 hk hs
      by_cases hbank : bank u = true
      · rw [if_pos hbank]
        cases iFuel with
        | zero =>
            have hdone :
                ((AdaptiveCircuit.done : AdaptiveCircuit CliffordT (s3_N n r b)).channelRef m_ref σ) =
                σ := by
              simp [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList]
            rw [hdone, s3_binomErr_zero_fuel R]
            exact s1.traceDist_density_le_two (s1.isDensityOperator_partialTraceAnc hσ) htarg_dens
        | succ f =>
            let bank' := Function.update bank u false
            have hne := s3_targ_ne_bank n r b 0 target u htarg
            have hpure_u : t9_HasPureWire (s3_bankWire n r b u) (resourceVec (s3_θks k 0)) σ := by
              have h := hanc.2.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
              dsimp only [s3_bankVec] at h
              rw [hbank, if_pos rfl] at h
              dsimp only [u] at h ⊢
              rwa [s3_θslot_slotOf r b k 0 hk hs] at h
            have hst := hstep (s3_N n r b) m_ref target (s3_bankWire n r b u) hne (s3_θks k 0) σ hpure_u
            dsimp only at hst
            have hsync_eq :
                s3_syncBankLe n r b m_ref bank' 0 hs σ =
                t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ := by
              dsimp only [s3_syncBankLe]
              have hres := s3_syncLevel_eq_single s2 bank' k hk 0 hs (σ := σ) (fun k'' hk'' => by
                let v := s3_slotOf r b k''.1 0 k''.2 hs
                have hne_vu : v ≠ u := by
                  intro h
                  apply hk''
                  have hk_eq := congrArg (s3_slotK r b) h
                  dsimp only [v, u] at hk_eq
                  rw [s3_slotK_slotOf, s3_slotK_slotOf] at hk_eq
                  exact Fin.ext hk_eq
                have heqb : bank' v = bank v := Function.update_of_ne hne_vu false bank
                have hv := hanc.2.1 v (by dsimp only [v]; rw [s3_slotS_slotOf])
                dsimp only [v] at heqb hv ⊢
                simpa [s3_bankVec, heqb] using hv)
              have hbu : bank' u = false := Function.update_self u false bank
              simpa [u, s3_bankVec, bank', hbu] using hres
            have hagree : ∀ v : Fin (s3_S r b), 0 < s3_slotS r b v → bank' v = bank v := by
              intro v hv
              have hne_vu : v ≠ u := by
                intro h
                subst h
                simp [u, s3_slotS_slotOf] at hv
              exact Function.update_of_ne hne_vu false bank
            let σ_F :=
              t9_unitConj (t9_rotOnWire (s3_θks k 0) target)
                (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)
            let σ_T :=
              t9_unitConj (t9_rotOnWire (-s3_θks k 0) target)
                (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)
            have hσ_T_eq : σ_T = σ_F := by
              dsimp only [σ_T, σ_F]
              rw [s3_rotOnWire_neg_θks_zero s2 k target]
            have hσ_F_eq : σ_F = t9_unitConj (t9_rotOnWire (s3_θks k 0) target)
                (s3_syncBankLe n r b m_ref bank' 0 hs σ) := by
              rw [hsync_eq]
            have hσF_dens : WildeQIT.IsDensityOperator σ_F :=
              s3_isDensityOperator_unitConj s1 (s3_rotOnWire_isUnitary _ _)
                (s3_t9_traceAndSetWire_isDensityOperator _ _ s2.norm_sq_plusVec hσ)
            have hch :
                t9_partialTraceAnc
                  ((AdaptiveCircuit.gate (cnotApp t9_cnot_mem_cliffordT target (s3_bankWire n r b u) hne)
                    (.measure (s3_bankWire n r b u) fun out =>
                      match out with
                      | false => t9_prependCircuit (s3_liftCircuit (s3_w1 (s3_bankWire n r b u)) resetFalse) (cont f bank')
                      | true => t9_prependCircuit (s3_liftCircuit (s3_w1 (s3_bankWire n r b u)) resetTrue) (cont f bank'))).channelRef m_ref σ) =
                ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) +
                ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) := by
              rw [s3_channelRef_gate, s3_channelRef_measure,
                s3_channelRef_prependCircuit, s3_channelRef_prependCircuit,
                s3_liftCircuit_unitary, s3_liftCircuit_unitary]
              dsimp only [s3_w1]
              rw [hst.1, hst.2, s3_channelRef_smul, s3_channelRef_smul,
                s3_partialTraceAnc_add, s3_partialTraceAnc_smul, s3_partialTraceAnc_smul]
              change ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) +
                ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_T) = _
              rw [hσ_T_eq]
            rw [hch]
            have hsub :
                (((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) +
                  ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F)) - target_mat =
                ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) := by
              have hhalf : ((1 / 2 : ℝ) : ℂ) • target_mat + ((1 / 2 : ℝ) : ℂ) • target_mat = target_mat := by
                rw [← add_smul]
                norm_num
              conv_lhs => rhs; rw [← hhalf]
              simp only [smul_sub]
              abel
            have hHerm : (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat).IsHermitian :=
              (s1.isHermitian_partialTraceAnc
                (s1.isHermitian_channelRef _ hσF_dens.1.isHermitian)).sub htarg_dens.1.isHermitian
            have hdist := hcont f (Nat.le_succ f) bank' hagree
            rw [← hσ_F_eq] at hdist
            have hle1 : WildeQIT.traceDist (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F)) target_mat ≤
                s3_binomErr f (R + 1) :=
              le_trans hdist (s3_binomErr_mono_right f (Nat.le_succ R))
            rw [WildeQIT.traceDist, hsub]
            have hadd := s1.traceNorm_add_le
              (s3_isHermitian_real_smul (1 / 2 : ℝ) hHerm)
              (s3_isHermitian_real_smul (1 / 2 : ℝ) hHerm)
            rw [s1.traceNorm_smul_of_nonneg (by norm_num) hHerm] at hadd
            calc WildeQIT.traceNorm
                  (((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                    ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat))
                ≤ (1 / 2 : ℝ) * WildeQIT.traceNorm (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                  (1 / 2 : ℝ) * WildeQIT.traceNorm (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) := hadd
              _ ≤ (1 / 2 : ℝ) * s3_binomErr f R + (1 / 2 : ℝ) * s3_binomErr f (R + 1) :=
                  add_le_add
                    (mul_le_mul_of_nonneg_left hdist (by norm_num))
                    (mul_le_mul_of_nonneg_left hle1 (by norm_num))
              _ = s3_binomErr (f + 1) (R + 1) := s3_binomErr_pascal f R
      · have hbf : bank u = false := Bool.eq_false_iff.mpr hbank
        rw [if_neg hbank]
        let bank_mid := Function.update bank u true
        let w4 := s3_w4 n r b hb hr k hk 0 hs target htarg
        have hw0 : t9_HasPureWire (w4 0) (resourceVec (s3_θks k 0)) σ := by
          have h := hanc.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
          have hw0_eq : w4 0 = s3_catWire n r b u := rfl
          rw [hw0_eq]
          dsimp only [u] at h ⊢
          rwa [s3_θslot_slotOf r b k 0 hk hs] at h
        have hw2 : t9_HasPureWire (w4 2) plusVec σ := by
          have h := hanc.2.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
          have hw2_eq : w4 2 = s3_bankWire n r b u := rfl
          rw [hw2_eq]
          dsimp only [s3_bankVec] at h
          rw [hbf] at h
          exact h
        have hw3 : t9_HasPureWire (w4 3) (basisVec false) σ :=
          hanc.2.2 ⟨0, hs⟩ le_rfl
        have hhalv := hsplit (s3_N n r b) m_ref w4 (s3_θks k 0) σ hw0 hw2 hw3
        have hrot1 : t9_rotOnWire (2 * s3_θks k 0) (w4 3) = 1 :=
          s3_rotOnWire_two_θks_zero s2 k (w4 3)
        rw [hrot1, s3_unitConj_one] at hhalv
        have hsync_eq :
            s3_syncBankLe n r b m_ref bank_mid 0 hs σ =
            t9_traceAndSetWire (s3_bankWire n r b u) (resourceVec (s3_θks k 0)) σ := by
          dsimp only [s3_syncBankLe]
          have hres := s3_syncLevel_eq_single s2 bank_mid k hk 0 hs (σ := σ) (fun k'' hk'' => by
            let v := s3_slotOf r b k''.1 0 k''.2 hs
            have hne_vu : v ≠ u := by
              intro h
              apply hk''
              have hk_eq := congrArg (s3_slotK r b) h
              dsimp only [v, u] at hk_eq
              rw [s3_slotK_slotOf, s3_slotK_slotOf] at hk_eq
              exact Fin.ext hk_eq
            have heqb : bank_mid v = bank v := Function.update_of_ne hne_vu true bank
            have hv := hanc.2.1 v (by dsimp only [v]; rw [s3_slotS_slotOf])
            dsimp only [v] at heqb hv ⊢
            simpa [s3_bankVec, heqb] using hv)
          have hbu : bank_mid u = true := Function.update_self u true bank
          simpa [u, s3_bankVec, bank_mid, hbu, s3_θslot_slotOf r b k 0 hk hs] using hres
        have hagree : ∀ v : Fin (s3_S r b), 0 < s3_slotS r b v → bank_mid v = bank v := by
          intro v hv
          have hne_vu : v ≠ u := by
            intro h
            subst h
            simp [u, s3_slotS_slotOf] at hv
          exact Function.update_of_ne hne_vu true bank
        rw [s3_channelRef_prependCircuit, s3_channelRef_prependCircuit,
          s3_liftCircuit_unitary, s3_liftCircuit_unitary, hhalv]
        change WildeQIT.traceDist
          (t9_partialTraceAnc ((cont iFuel bank_mid).channelRef m_ref
            (t9_unitConj (t9_rotOnWire (s3_θks k 0) target)
              (t9_traceAndSetWire (s3_bankWire n r b u) (resourceVec (s3_θks k 0)) σ))))
          target_mat ≤ s3_binomErr iFuel (R + 1)
        rw [← hsync_eq]
        exact le_trans (hcont iFuel le_rfl bank_mid hagree)
          (s3_binomErr_mono_right iFuel (Nat.le_succ R))
  | s' + 1, hs, target, htarg, iFuel, bank, cont, m_ref, σ, target_mat, R, hσ, hanc, htarg_dens, hcont => by
      dsimp only [s3_compileRot]
      let u := s3_slotOf r b k (s' + 1) hk hs
      by_cases hbank : bank u = true
      · rw [if_pos hbank]
        cases iFuel with
        | zero =>
            have hdone :
                ((AdaptiveCircuit.done : AdaptiveCircuit CliffordT (s3_N n r b)).channelRef m_ref σ) =
                σ := by
              simp [AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList]
            rw [hdone, s3_binomErr_zero_fuel R]
            exact s1.traceDist_density_le_two (s1.isDensityOperator_partialTraceAnc hσ) htarg_dens
        | succ f =>
            let bank' := Function.update bank u false
            have hne := s3_targ_ne_bank n r b (s' + 1) target u htarg
            have hpure_u :
                t9_HasPureWire (s3_bankWire n r b u) (resourceVec (s3_θks k (s' + 1))) σ := by
              have h := hanc.2.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
              dsimp only [s3_bankVec] at h
              rw [hbank, if_pos rfl] at h
              dsimp only [u] at h ⊢
              rwa [s3_θslot_slotOf r b k (s' + 1) hk hs] at h
            have hst := hstep (s3_N n r b) m_ref target (s3_bankWire n r b u) hne
              (s3_θks k (s' + 1)) σ hpure_u
            dsimp only at hst
            have hagree : ∀ v : Fin (s3_S r b), s' + 1 < s3_slotS r b v → bank' v = bank v := by
              intro v hv
              have hne_vu : v ≠ u := by
                intro h; subst h; simp [u, s3_slotS_slotOf] at hv
              exact Function.update_of_ne hne_vu false bank
            have hsync_F :
                s3_syncBankLe n r b m_ref bank' (s' + 1) hs σ =
                t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ := by
              dsimp only [s3_syncBankLe]
              have hsync_s' :
                  s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ = σ := by
                have hlev : ∀ (k' : ℕ) (hk' : k' < s3_M b r) (l : List (Fin (s3_B b)))
                    (σ₀ : Matrix (Fin m_ref × Qubits (s3_N n r b))
                      (Fin m_ref × Qubits (s3_N n r b)) ℂ),
                    (∀ a ∈ l, t9_HasPureWire
                      (s3_bankWire n r b (s3_slotOf r b a.1 k' a.2 hk'))
                      (s3_bankVec r b bank' (s3_slotOf r b a.1 k' a.2 hk')) σ₀) →
                    l.foldr (fun k'' acc =>
                      let v := s3_slotOf r b k''.1 k' k''.2 hk'
                      t9_traceAndSetWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) acc) σ₀ = σ₀ := by
                  intro k' hk' l σ₀ hl
                  induction l with
                  | nil => rfl
                  | cons a as ihl =>
                      dsimp only [List.foldr_cons]
                      rw [ihl (fun x hx => hl x (List.mem_cons_of_mem a hx))]
                      exact hl a List.mem_cons_self
                have hgen : ∀ (k_s : ℕ) (hk_s : k_s < s3_M b r), k_s ≤ s' →
                    s3_syncBankLe n r b m_ref bank' k_s hk_s σ = σ := by
                  intro k_s hk_s hle
                  induction k_s with
                  | zero =>
                      dsimp only [s3_syncBankLe, s3_syncLevel]
                      refine hlev 0 hk_s (List.finRange (s3_B b)) σ fun a _ => ?_
                      let v := s3_slotOf r b a.1 0 a.2 hk_s
                      have hne_vu : v ≠ u := by
                        intro h
                        have := congrArg (s3_slotS r b) h
                        simp [v, u, s3_slotS_slotOf] at this
                      have heqb : bank' v = bank v := Function.update_of_ne hne_vu false bank
                      have hv := hanc.2.1 v (by simp [v, s3_slotS_slotOf])
                      dsimp only [v] at heqb hv ⊢
                      simpa [s3_bankVec, heqb] using hv
                  | succ j ihj =>
                      dsimp only [s3_syncBankLe]
                      rw [ihj (Nat.lt_of_succ_lt hk_s) (Nat.le_of_succ_le hle)]
                      dsimp only [s3_syncLevel]
                      refine hlev (j + 1) hk_s (List.finRange (s3_B b)) σ fun a _ => ?_
                      let v := s3_slotOf r b a.1 (j + 1) a.2 hk_s
                      have hne_vu : v ≠ u := by
                        intro h
                        have := congrArg (s3_slotS r b) h
                        simp [v, u, s3_slotS_slotOf] at this
                        omega
                      have heqb : bank' v = bank v := Function.update_of_ne hne_vu false bank
                      have hv := hanc.2.1 v (by simp [v, s3_slotS_slotOf]; omega)
                      dsimp only [v] at heqb hv ⊢
                      simpa [s3_bankVec, heqb] using hv
                exact hgen s' (Nat.lt_of_succ_lt hs) le_rfl
              rw [hsync_s']
              have hres := s3_syncLevel_eq_single s2 bank' k hk (s' + 1) hs (σ := σ) (fun k'' hk'' => by
                let v := s3_slotOf r b k''.1 (s' + 1) k''.2 hs
                have hne_vu : v ≠ u := by
                  intro h
                  apply hk''
                  have hk_eq := congrArg (s3_slotK r b) h
                  dsimp only [v, u] at hk_eq
                  rw [s3_slotK_slotOf, s3_slotK_slotOf] at hk_eq
                  exact Fin.ext hk_eq
                have heqb : bank' v = bank v := Function.update_of_ne hne_vu false bank
                have hv := hanc.2.1 v (by dsimp only [v]; rw [s3_slotS_slotOf])
                dsimp only [v] at heqb hv ⊢
                simpa [s3_bankVec, heqb] using hv)
              have hbu : bank' u = false := Function.update_self u false bank
              simpa [u, s3_bankVec, bank', hbu] using hres
            let σ_F :=
              t9_unitConj (t9_rotOnWire (s3_θks k (s' + 1)) target)
                (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)
            let σ_T :=
              t9_unitConj (t9_rotOnWire (-s3_θks k (s' + 1)) target)
                (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)
            have hσF_dens : WildeQIT.IsDensityOperator σ_F :=
              s3_isDensityOperator_unitConj s1 (s3_rotOnWire_isUnitary _ _)
                (s3_t9_traceAndSetWire_isDensityOperator _ _ s2.norm_sq_plusVec hσ)
            have hσT_dens : WildeQIT.IsDensityOperator σ_T :=
              s3_isDensityOperator_unitConj s1 (s3_rotOnWire_isUnitary _ _)
                (s3_t9_traceAndSetWire_isDensityOperator _ _ s2.norm_sq_plusVec hσ)
            have hσT_anc : s3_HasAncStateLe n r b s' bank' σ_T := by
              have h1 : s3_HasAncStateLe n r b s' bank'
                  (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ) := by
                refine ⟨fun v hv => ?_, fun v hv => ?_, fun t ht => ?_⟩
                · exact s2.hasPureWire_traceAndSet_other
                    (s3_catWire_ne_bankWire n r b v u).symm _ _ (hanc.1 v (Nat.le_succ_of_le hv))
                · have hne_vu : v ≠ u := by
                    intro h; subst h; simp [u, s3_slotS_slotOf] at hv
                  have heqb : bank' v = bank v := Function.update_of_ne hne_vu false bank
                  have hne_w : s3_bankWire n r b u ≠ s3_bankWire n r b v :=
                    fun h => hne_vu ((s3_bankWire_inj n r b).mp h).symm
                  simpa [s3_bankVec, heqb] using
                    s2.hasPureWire_traceAndSet_other hne_w _ _ (hanc.2.1 v (Nat.le_succ_of_le hv))
                · exact s2.hasPureWire_traceAndSet_other
                    (s3_bankWire_ne_scratchWire n r b u t) _ _ (hanc.2.2 t (Nat.le_succ_of_le ht))
              refine s3_HasAncStateLe_unitConj_embedOp s2 _ _
                (fun v _ => by
                  rintro ⟨i, hi⟩
                  change target = s3_catWire n r b v at hi
                  exact s3_targ_ne_cat n r b (s' + 1) target v htarg hi)
                (fun v _ => by
                  rintro ⟨i, hi⟩
                  change target = s3_bankWire n r b v at hi
                  exact s3_targ_ne_bank n r b (s' + 1) target v htarg hi)
                (fun t ht => by
                  rintro ⟨i, hi⟩
                  change target = s3_scratchWire n r b t at hi
                  exact s3_targ_ne_scratch n r b (s' + 1) target t (Nat.le_succ_of_le ht) htarg hi)
                h1
            let subT :=
              s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr k hk s'
                (Nat.lt_of_succ_lt hs) target (s3_ValidTarget_pred htarg) f bank' cont
            have hdist_F :
                WildeQIT.traceDist (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F))
                  target_mat ≤ s3_binomErr f R := by
              have := hcont f (Nat.le_succ f) bank' hagree
              rwa [hsync_F] at this
            have hdist_T :
                WildeQIT.traceDist (t9_partialTraceAnc (subT.channelRef m_ref σ_T))
                  target_mat ≤ s3_binomErr f (R + 1) := by
              refine s3_compileRot_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
                n r b hb hr k hk s' (Nat.lt_of_succ_lt hs) target (s3_ValidTarget_pred htarg)
                f bank' cont m_ref σ_T target_mat R hσT_dens hσT_anc htarg_dens ?_
              intro f'' hf'' bank'' hagree''
              have hagree_outer :
                  ∀ v : Fin (s3_S r b), s' + 1 < s3_slotS r b v → bank'' v = bank v := by
                intro v hv
                rw [hagree'' v (Nat.lt_of_succ_lt hv)]
                exact hagree v hv
              have hsync_mid :
                  t9_unitConj (t9_rotOnWire (s3_θks k s') target)
                    (s3_syncBankLe n r b m_ref bank'' s' (Nat.lt_of_succ_lt hs) σ_T) =
                  t9_unitConj (t9_rotOnWire (s3_θks k (s' + 1)) target)
                    (s3_syncBankLe n r b m_ref bank'' (s' + 1) hs σ) := by
                dsimp only [σ_T]
                have hcomm1 :
                    s3_syncBankLe n r b m_ref bank'' s' (Nat.lt_of_succ_lt hs)
                      (t9_unitConj (t9_rotOnWire (-s3_θks k (s' + 1)) target)
                        (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)) =
                    t9_unitConj (t9_rotOnWire (-s3_θks k (s' + 1)) target)
                      (s3_syncBankLe n r b m_ref bank'' s' (Nat.lt_of_succ_lt hs)
                        (t9_traceAndSetWire (s3_bankWire n r b u) plusVec σ)) :=
                  s3_syncBankLe_comm_embedOp s2 _ _ bank'' s' (Nat.lt_of_succ_lt hs)
                    (fun v _ => by
                      rintro ⟨i, hi⟩
                      change target = s3_bankWire n r b v at hi
                      exact s3_targ_ne_bank n r b (s' + 1) target v htarg hi) _
                rw [hcomm1, ← s3_unitConj_mul, s3_rotOnWire_succ_mul_neg s2 k s' target,
                  s3_syncBankLe_comm_wire n r b m_ref bank'' s' (Nat.lt_of_succ_lt hs)
                    (fun v hv => by
                      intro h
                      rw [s3_bankWire_inj] at h
                      subst h
                      simp [u, s3_slotS_slotOf] at hv)]
                congr 1
                dsimp only [s3_syncBankLe]
                have hres := s3_syncLevel_eq_single s2 bank'' k hk (s' + 1) hs
                  (σ := s3_syncBankLe n r b m_ref bank'' s' (Nat.lt_of_succ_lt hs) σ)
                  (fun k'' hk'' => by
                    let v := s3_slotOf r b k''.1 (s' + 1) k''.2 hs
                    have hne_vu : v ≠ u := by
                      intro h
                      apply hk''
                      have hk_eq := congrArg (s3_slotK r b) h
                      dsimp only [v, u] at hk_eq
                      rw [s3_slotK_slotOf, s3_slotK_slotOf] at hk_eq
                      exact Fin.ext hk_eq
                    have heqb : bank'' v = bank v := by
                      have h1 := hagree'' v (by dsimp only [v]; rw [s3_slotS_slotOf]; exact lt_add_one s')
                      have h2 := Function.update_of_ne hne_vu false bank
                      exact h1.trans h2
                    have hp_orig : t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank'' v) σ := by
                      have hv := hanc.2.1 v (by dsimp only [v]; rw [s3_slotS_slotOf])
                      dsimp only [v] at heqb hv ⊢
                      simpa [s3_bankVec, heqb] using hv
                    exact s3_syncBankLe_preserves_other_pure s2 bank'' s' (Nat.lt_of_succ_lt hs)
                      (fun w hw => by
                        intro h; rw [s3_bankWire_inj] at h; subst h
                        simp [s3_slotS_slotOf] at hw) _ hp_orig)
                have hbanku : bank'' u = false := by
                  have h1 := hagree'' u (by dsimp only [u]; rw [s3_slotS_slotOf]; exact lt_add_one s')
                  simpa [bank'] using h1
                simpa [u, s3_bankVec, hbanku] using hres.symm
              rw [hsync_mid]
              exact hcont f'' (le_trans hf'' (Nat.le_succ f)) bank'' hagree_outer
            have hch :
                t9_partialTraceAnc
                  ((AdaptiveCircuit.gate (cnotApp t9_cnot_mem_cliffordT target (s3_bankWire n r b u) hne)
                    (.measure (s3_bankWire n r b u) fun out =>
                      match out with
                      | false => t9_prependCircuit (s3_liftCircuit (s3_w1 (s3_bankWire n r b u)) resetFalse) (cont f bank')
                      | true => t9_prependCircuit (s3_liftCircuit (s3_w1 (s3_bankWire n r b u)) resetTrue) subT)).channelRef m_ref σ) =
                ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) +
                ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc (subT.channelRef m_ref σ_T) := by
              rw [s3_channelRef_gate, s3_channelRef_measure,
                s3_channelRef_prependCircuit, s3_channelRef_prependCircuit,
                s3_liftCircuit_unitary, s3_liftCircuit_unitary]
              dsimp only [s3_w1]
              rw [hst.1, hst.2, s3_channelRef_smul, s3_channelRef_smul,
                s3_partialTraceAnc_add, s3_partialTraceAnc_smul, s3_partialTraceAnc_smul]
            rw [hch]
            have hsub :
                (((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) +
                  ((1 / 2 : ℝ) : ℂ) • t9_partialTraceAnc (subT.channelRef m_ref σ_T)) - target_mat =
                ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc (subT.channelRef m_ref σ_T) - target_mat) := by
              have hhalf : ((1 / 2 : ℝ) : ℂ) • target_mat + ((1 / 2 : ℝ) : ℂ) • target_mat = target_mat := by
                rw [← add_smul]
                norm_num
              conv_lhs => rhs; rw [← hhalf]
              simp only [smul_sub]
              abel
            have hHermF : (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat).IsHermitian :=
              (s1.isHermitian_partialTraceAnc
                (s1.isHermitian_channelRef _ hσF_dens.1.isHermitian)).sub htarg_dens.1.isHermitian
            have hHermT : (t9_partialTraceAnc (subT.channelRef m_ref σ_T) - target_mat).IsHermitian :=
              (s1.isHermitian_partialTraceAnc
                (s1.isHermitian_channelRef _ hσT_dens.1.isHermitian)).sub htarg_dens.1.isHermitian
            rw [WildeQIT.traceDist, hsub]
            have hadd := s1.traceNorm_add_le
              (s3_isHermitian_real_smul (1 / 2 : ℝ) hHermF)
              (s3_isHermitian_real_smul (1 / 2 : ℝ) hHermT)
            rw [s1.traceNorm_smul_of_nonneg (by norm_num) hHermF,
              s1.traceNorm_smul_of_nonneg (by norm_num) hHermT] at hadd
            calc WildeQIT.traceNorm
                  (((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                    ((1 / 2 : ℝ) : ℂ) • (t9_partialTraceAnc (subT.channelRef m_ref σ_T) - target_mat))
                ≤ (1 / 2 : ℝ) * WildeQIT.traceNorm (t9_partialTraceAnc ((cont f bank').channelRef m_ref σ_F) - target_mat) +
                  (1 / 2 : ℝ) * WildeQIT.traceNorm (t9_partialTraceAnc (subT.channelRef m_ref σ_T) - target_mat) := hadd
              _ ≤ (1 / 2 : ℝ) * s3_binomErr f R + (1 / 2 : ℝ) * s3_binomErr f (R + 1) :=
                  add_le_add
                    (mul_le_mul_of_nonneg_left hdist_F (by norm_num))
                    (mul_le_mul_of_nonneg_left hdist_T (by norm_num))
              _ = s3_binomErr (f + 1) (R + 1) := s3_binomErr_pascal f R
      · have hbf : bank u = false := Bool.eq_false_iff.mpr hbank
        rw [if_neg hbank]
        let bank_mid := Function.update bank u true
        let w4 := s3_w4 n r b hb hr k hk (s' + 1) hs target htarg
        let σ₁ := t9_unitConj (embedOp half1.unitary w4) σ
        have hσ₁_dens : WildeQIT.IsDensityOperator σ₁ :=
          s3_isDensityOperator_unitConj s1
            (s3_embedOp_isUnitary (s3_circuit_unitary_isUnitary s1.cliffordT_isUnitary half1) w4) hσ
        have hw4_disj_cat : ∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s' →
            s3_catWire n r b v ∉ Set.range w4 := by
          intro v hv hmem
          rcases hmem with ⟨i, hi⟩
          dsimp only [w4, s3_w4] at hi
          fin_cases i
          · change s3_catWire n r b u = s3_catWire n r b v at hi
            rw [s3_catWire_inj] at hi
            subst hi
            simp [u, s3_slotS_slotOf] at hv
          · change target = s3_catWire n r b v at hi
            exact s3_targ_ne_cat n r b (s' + 1) target v htarg hi
          · change s3_bankWire n r b u = s3_catWire n r b v at hi
            exact s3_catWire_ne_bankWire n r b v u hi.symm
          · change s3_scratchWire n r b ⟨s' + 1, hs⟩ = s3_catWire n r b v at hi
            exact s3_catWire_ne_scratchWire n r b v ⟨s' + 1, hs⟩ hi.symm
        have hw4_disj_bank : ∀ v : Fin (s3_S r b), s3_slotS r b v ≤ s' →
            s3_bankWire n r b v ∉ Set.range w4 := by
          intro v hv hmem
          rcases hmem with ⟨i, hi⟩
          dsimp only [w4, s3_w4] at hi
          fin_cases i
          · change s3_catWire n r b u = s3_bankWire n r b v at hi
            exact s3_catWire_ne_bankWire n r b u v hi
          · change target = s3_bankWire n r b v at hi
            exact s3_targ_ne_bank n r b (s' + 1) target v htarg hi
          · change s3_bankWire n r b u = s3_bankWire n r b v at hi
            rw [s3_bankWire_inj] at hi
            subst hi
            simp [u, s3_slotS_slotOf] at hv
          · change s3_scratchWire n r b ⟨s' + 1, hs⟩ = s3_bankWire n r b v at hi
            exact s3_bankWire_ne_scratchWire n r b v ⟨s' + 1, hs⟩ hi.symm
        have hw4_disj_scr : ∀ t : Fin (s3_M b r), t.1 ≤ s' →
            s3_scratchWire n r b t ∉ Set.range w4 := by
          intro t ht hmem
          rcases hmem with ⟨i, hi⟩
          dsimp only [w4, s3_w4] at hi
          fin_cases i
          · change s3_catWire n r b u = s3_scratchWire n r b t at hi
            exact s3_catWire_ne_scratchWire n r b u t hi
          · change target = s3_scratchWire n r b t at hi
            exact s3_targ_ne_scratch n r b (s' + 1) target t (Nat.le_succ_of_le ht) htarg hi
          · change s3_bankWire n r b u = s3_scratchWire n r b t at hi
            exact s3_bankWire_ne_scratchWire n r b u t hi
          · change s3_scratchWire n r b ⟨s' + 1, hs⟩ = s3_scratchWire n r b t at hi
            rw [s3_scratchWire_inj] at hi
            have := congrArg Fin.val hi
            simp at this
            omega
        have hanc₁ : s3_HasAncStateLe n r b s' bank_mid σ₁ := by
          have hanc_pre : s3_HasAncStateLe n r b s' bank_mid σ := by
            refine ⟨fun v hv => hanc.1 v (Nat.le_succ_of_le hv), fun v hv => ?_,
              fun t ht => hanc.2.2 t (Nat.le_succ_of_le ht)⟩
            have hne_vu : v ≠ u := by intro h; subst h; simp [u, s3_slotS_slotOf] at hv
            have heqb : bank_mid v = bank v := Function.update_of_ne hne_vu true bank
            simpa [s3_bankVec, heqb] using hanc.2.1 v (Nat.le_succ_of_le hv)
          exact s3_HasAncStateLe_unitConj_embedOp s2 half1.unitary w4
            hw4_disj_cat hw4_disj_bank hw4_disj_scr hanc_pre
        let cont' : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b) :=
          fun iFuel' bank' => t9_prependCircuit (s3_liftCircuit w4 half2) (cont iFuel' bank')
        rw [s3_channelRef_prependCircuit, s3_liftCircuit_unitary]
        refine s3_compileRot_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
          n r b hb hr k hk s' (Nat.lt_of_succ_lt hs)
          (s3_scratchWire n r b ⟨s' + 1, hs⟩) (s3_ValidTarget_scratch n r b s' hs)
          iFuel bank_mid cont' m_ref σ₁ target_mat R hσ₁_dens hanc₁ htarg_dens ?_
        intro f' hf' bank' hagree_mid
        dsimp only [cont']
        rw [s3_channelRef_prependCircuit, s3_liftCircuit_unitary]
        let σ_sync := s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ
        have hsync_comm :
            s3_syncBankLe n r b m_ref bank' s' (Nat.lt_of_succ_lt hs) σ₁ =
            t9_unitConj (embedOp half1.unitary w4) σ_sync :=
          s3_syncBankLe_comm_embedOp s2 half1.unitary w4 bank' s' (Nat.lt_of_succ_lt hs)
            hw4_disj_bank σ
        rw [hsync_comm]
        have hw0 : t9_HasPureWire (w4 0) (resourceVec (s3_θks k (s' + 1))) σ_sync := by
          have hp0 : t9_HasPureWire (w4 0) (resourceVec (s3_θks k (s' + 1))) σ := by
            have h := hanc.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
            have hw0_eq : w4 0 = s3_catWire n r b u := rfl
            rw [hw0_eq]
            dsimp only [u] at h ⊢
            rwa [s3_θslot_slotOf r b k (s' + 1) hk hs] at h
          exact s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
            (fun v _ => (s3_catWire_ne_bankWire n r b u v)) _ hp0
        have hw2 : t9_HasPureWire (w4 2) plusVec σ_sync := by
          have hp2 : t9_HasPureWire (w4 2) plusVec σ := by
            have h := hanc.2.1 u (by dsimp only [u]; rw [s3_slotS_slotOf])
            have hw2_eq : w4 2 = s3_bankWire n r b u := rfl
            rw [hw2_eq]
            dsimp only [s3_bankVec] at h
            rw [hbf] at h
            exact h
          exact s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
            (fun v hv => by
              intro h
              have hw2_eq : w4 2 = s3_bankWire n r b u := rfl
              rw [hw2_eq, s3_bankWire_inj] at h; subst h
              simp [u, s3_slotS_slotOf] at hv) _ hp2
        have hw3 : t9_HasPureWire (w4 3) (basisVec false) σ_sync := by
          have hp3 : t9_HasPureWire (w4 3) (basisVec false) σ := hanc.2.2 ⟨s' + 1, hs⟩ le_rfl
          exact s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
            (fun v _ => (s3_bankWire_ne_scratchWire n r b v ⟨s' + 1, hs⟩).symm) _ hp3
        have hhalv := hsplit (s3_N n r b) m_ref w4 (s3_θks k (s' + 1)) σ_sync hw0 hw2 hw3
        have hw3_eq : w4 3 = s3_scratchWire n r b ⟨s' + 1, hs⟩ := rfl
        have hw1_eq : w4 1 = target := rfl
        have hw2_eq : w4 2 = s3_bankWire n r b u := rfl
        rw [s3_two_mul_θks_succ k s', hw3_eq, hw1_eq, hw2_eq] at hhalv
        rw [hhalv]
        have hsync_top :
            t9_traceAndSetWire (s3_bankWire n r b u) (resourceVec (s3_θks k (s' + 1))) σ_sync =
            s3_syncBankLe n r b m_ref bank' (s' + 1) hs σ := by
          dsimp only [s3_syncBankLe]
          have hres := s3_syncLevel_eq_single s2 bank' k hk (s' + 1) hs (σ := σ_sync)
            (fun k'' hk'' => by
              let v := s3_slotOf r b k''.1 (s' + 1) k''.2 hs
              have hne_vu : v ≠ u := by
                intro h
                apply hk''
                have hk_eq := congrArg (s3_slotK r b) h
                dsimp only [v, u] at hk_eq
                rw [s3_slotK_slotOf, s3_slotK_slotOf] at hk_eq
                exact Fin.ext hk_eq
              have heqb : bank' v = bank v := by
                have h1 := hagree_mid v (by dsimp only [v]; rw [s3_slotS_slotOf]; exact lt_add_one s')
                have h2 := Function.update_of_ne hne_vu true bank
                exact h1.trans h2
              have hp_orig : t9_HasPureWire (s3_bankWire n r b v) (s3_bankVec r b bank' v) σ := by
                have hv := hanc.2.1 v (by dsimp only [v]; rw [s3_slotS_slotOf])
                dsimp only [v] at heqb hv ⊢
                simpa [s3_bankVec, heqb] using hv
              exact s3_syncBankLe_preserves_other_pure s2 bank' s' (Nat.lt_of_succ_lt hs)
                (fun w hw => by
                  intro h; rw [s3_bankWire_inj] at h; subst h
                  simp [s3_slotS_slotOf] at hw) _ hp_orig)
          have hbanku : bank' u = true := by
            have h1 := hagree_mid u (by dsimp only [u]; rw [s3_slotS_slotOf]; exact lt_add_one s')
            simpa [bank_mid] using h1
          have hu_eq : s3_θslot r b u = s3_θks k (s' + 1) := s3_θslot_slotOf r b k (s' + 1) hk hs
          simpa [u, s3_bankVec, hbanku, hu_eq] using hres.symm
        rw [hsync_top]
        have hagree_outer :
            ∀ v : Fin (s3_S r b), s' + 1 < s3_slotS r b v → bank' v = bank v := by
          intro v hv
          have hne_vu : v ≠ u := by intro h; subst h; simp [u, s3_slotS_slotOf] at hv
          rw [hagree_mid v (Nat.lt_of_succ_lt hv)]
          exact Function.update_of_ne hne_vu true bank
        exact hcont f' hf' bank' hagree_outer

/-! ### Block E: Chaining rotations, compiling A, and main theorem -/

private noncomputable def s3_compileRotList
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r)
    (j : ℕ) (q : Fin n) :
    List (Fin r) → ℕ → s3_Bank r b → (ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b)) →
    AdaptiveCircuit CliffordT (s3_N n r b)
  | [], f, bank, cont => cont f bank
  | ℓ :: ℓs, f, bank, cont =>
      s3_compileRot resetFalse resetTrue half1 half2 n r b hb hr
        (s3_digit (s3_B b) j ℓ.1) (s3_digit_lt (s3_B b) j ℓ.1 (s3_B_pos b))
        (s3_levelOf b r ℓ) (s3_levelOf_lt b r hb ℓ)
        (s3_dataWire n r b q) (s3_ValidTarget_dataWire n r b _ q)
        f bank
        (fun f' bank' =>
          s3_compileRotList resetFalse resetTrue half1 half2 n r b hb hr j q ℓs f' bank' cont)

private theorem s3_compileRotList_maxGates
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hrF : resetFalse.size ≤ 1) (hrT : resetTrue.size ≤ 5)
    (hh1 : half1.size ≤ 38) (hh2 : half2.size ≤ 36)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) (j : ℕ) (q : Fin n) :
    ∀ (ℓs : List (Fin r)) (f : ℕ) (bank : s3_Bank r b)
      (cont : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b)) (K_base : ℕ),
      (∀ f' b', (cont f' b').maxGates ≤ K_base + 74 * s3_pot f' b') →
      (s3_compileRotList resetFalse resetTrue half1 half2 n r b hb hr j q ℓs f bank cont).maxGates ≤
        K_base + 74 * s3_pot f bank
  | [], f, bank, cont, _, hcont => hcont f bank
  | ℓ :: ℓs, f, bank, cont, K_base, hcont => by
      dsimp only [s3_compileRotList]
      refine s3_compileRot_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
        n r b hb hr _ _ _ _ _ _ f bank _ K_base ?_
      intro f' b'
      exact s3_compileRotList_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
        n r b hb hr j q ℓs f' b' cont K_base hcont

private noncomputable def s3_sumAngles (b r j : ℕ) (ℓs : List (Fin r)) : ℝ :=
  (ℓs.map fun ℓ => s3_θks (s3_digit (s3_B b) j ℓ.1) (s3_levelOf b r ℓ)).sum

private theorem s3_compileRotList_close (s1 : Thm9Step1API) (s2 : Thm9Step2API)
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hstep :
      ∀ (N m_ref : ℕ) (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire w_bank (resourceVec θ) σ →
        let w1_bank : Fin 1 ↪ Fin N := ⟨fun _ => w_bank, fun i j _ => Subsingleton.elim i j⟩
        let g_cnot := cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne
        let σ_cnot := t9_unitConj (embedOp g_cnot.gate.mat g_cnot.wires) σ
        let P (b : Bool) := AdaptiveCircuit.proj w_bank b
        t9_unitConj (embedOp resetFalse.unitary w1_bank) (t9_unitConj (P false) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire θ w_targ) (t9_traceAndSetWire w_bank plusVec σ) ∧
        t9_unitConj (embedOp resetTrue.unitary w1_bank) (t9_unitConj (P true) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire (-θ) w_targ) (t9_traceAndSetWire w_bank plusVec σ))
    (hsplit :
      ∀ (N m_ref : ℕ) (w : Fin 4 ↪ Fin N) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire (w 0) (resourceVec θ) σ →
        t9_HasPureWire (w 2) plusVec σ →
        t9_HasPureWire (w 3) (basisVec false) σ →
        t9_unitConj (embedOp half2.unitary w)
          (t9_unitConj (t9_rotOnWire (2 * θ) (w 3))
            (t9_unitConj (embedOp half1.unitary w) σ)) =
          t9_unitConj (t9_rotOnWire θ (w 1))
            (t9_traceAndSetWire (w 2) (resourceVec θ) σ))
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) (j : ℕ) (q : Fin n) :
    ∀ (ℓs : List (Fin r)) (f : ℕ) (bank : s3_Bank r b)
      (cont : ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b))
      (m_ref : ℕ)
      (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ)
      (target_mat : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ)
      (R : ℕ),
      WildeQIT.IsDensityOperator σ →
      s3_HasAncStateLe n r b (s3_M b r - 1) bank σ →
      WildeQIT.IsDensityOperator target_mat →
      (∀ (f' : ℕ), f' ≤ f → ∀ (bank' : s3_Bank r b)
        (σ_end : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
        WildeQIT.IsDensityOperator σ_end →
        s3_HasAncStateLe n r b (s3_M b r - 1) bank' σ_end →
        t9_partialTraceAnc σ_end =
          t9_unitConj (t9_rotOnWire (s3_sumAngles b r j ℓs) q) (t9_partialTraceAnc σ) →
        WildeQIT.traceDist (t9_partialTraceAnc ((cont f' bank').channelRef m_ref σ_end))
          target_mat ≤ s3_binomErr f' R) →
      WildeQIT.traceDist
        (t9_partialTraceAnc
          ((s3_compileRotList resetFalse resetTrue half1 half2 n r b hb hr j q ℓs f bank cont).channelRef m_ref σ))
        target_mat ≤ s3_binomErr f (R + ℓs.length)
  | [], f, bank, cont, m_ref, σ, target_mat, R, hσ, hanc, htarg_dens, hcont => by
      dsimp only [s3_compileRotList, List.length_nil, Nat.add_zero]
      refine hcont f le_rfl bank σ hσ hanc ?_
      simp [s3_sumAngles, s2.rotOnWire_zero, s3_unitConj_one]
  | ℓ :: ℓs, f, bank, cont, m_ref, σ, target_mat, R, hσ, hanc, htarg_dens, hcont => by
      dsimp only [s3_compileRotList]
      let k := s3_digit (s3_B b) j ℓ.1
      have hk := s3_digit_lt (s3_B b) j ℓ.1 (s3_B_pos b)
      let s := s3_levelOf b r ℓ
      have hs := s3_levelOf_lt b r hb ℓ
      have hs_le : s ≤ s3_M b r - 1 := by omega
      have hanc_s : s3_HasAncStateLe n r b s bank σ := s3_HasAncStateLe_mono hs_le hanc
      rw [show R + (ℓ :: ℓs).length = (R + ℓs.length) + 1 by simp; omega]
      refine s3_compileRot_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
        n r b hb hr k hk s hs (s3_dataWire n r b q) (s3_ValidTarget_dataWire n r b s q)
        f bank (fun f' bank' =>
          s3_compileRotList resetFalse resetTrue half1 half2 n r b hb hr j q ℓs f' bank' cont)
        m_ref σ target_mat (R + ℓs.length) hσ hanc_s htarg_dens ?_
      intro f₁ hf₁ bank₁ hagree₁
      let σ₁ :=
        t9_unitConj (t9_rotOnWire (s3_θks k s) (s3_dataWire n r b q))
          (s3_syncBankLe n r b m_ref bank₁ s hs σ)
      have hσ₁_dens : WildeQIT.IsDensityOperator σ₁ :=
        s3_isDensityOperator_unitConj s1 (s3_rotOnWire_isUnitary _ _)
          (s3_syncBankLe_isDensityOperator s2 bank₁ s hs hσ)
      have hanc₁ : s3_HasAncStateLe n r b (s3_M b r - 1) bank₁ σ₁ := by
        have hsync_anc := s3_syncBankLe_preserves_HasAncStateLe s2 bank bank₁ s hs hagree₁ hanc
        exact s3_HasAncStateLe_unitConj_data s2
          (Gate.ofMatrix1 (rot (s3_θks k s))).mat (s3_w1 q) hsync_anc
      have hpt₁ :
          t9_partialTraceAnc σ₁ =
          t9_unitConj (t9_rotOnWire (s3_θks k s) q) (t9_partialTraceAnc σ) := by
        dsimp only [σ₁]
        have hdata := s3_partialTraceAnc_unitConj_embedOp_data
          (Gate.ofMatrix1 (rot (s3_θks k s))).mat (s3_w1 q)
          (s3_syncBankLe n r b m_ref bank₁ s hs σ)
        change t9_partialTraceAnc
          (t9_unitConj (embedOp (Gate.ofMatrix1 (rot (s3_θks k s))).mat
            ((s3_w1 q).trans (s3_dataWireEmb n r b)))
            (s3_syncBankLe n r b m_ref bank₁ s hs σ)) = _ at hdata
        have hw_eq : (s3_w1 q).trans (s3_dataWireEmb n r b) = s3_w1 (s3_dataWire n r b q) := by
          ext i; rfl
        rw [hw_eq] at hdata
        dsimp only [t9_rotOnWire, s3_w1] at hdata ⊢
        rw [hdata, s3_syncBankLe_partialTraceAnc s2 bank₁ s hs σ]
      refine s3_compileRotList_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
        n r b hb hr j q ℓs f₁ bank₁ cont m_ref σ₁ target_mat R hσ₁_dens hanc₁ htarg_dens ?_
      intro f' hf' bank' σ_end hσ_end_dens hanc_end hpt_end
      refine hcont f' (le_trans hf' hf₁) bank' σ_end hσ_end_dens hanc_end ?_
      rw [hpt_end, hpt₁, ← s3_unitConj_mul, ← s2.rotOnWire_add]
      have hsum_eq : s3_sumAngles b r j ℓs + s3_θks k s = s3_sumAngles b r j (ℓ :: ℓs) := by
        simp [s3_sumAngles, k, s, add_comm]
      rw [hsum_eq]

private noncomputable def s3_compileA
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) :
    AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n →
    ℕ → s3_Bank r b → AdaptiveCircuit CliffordT (s3_N n r b)
  | .done, _, _ => .done
  | .measure q next, f, bank =>
      .measure (s3_dataWire n r b q) (fun out =>
        s3_compileA resetFalse resetTrue half1 half2 n r b hb hr (next out) f bank)
  | .gate g next, f, bank =>
      letI := Classical.propDecidable
      if hg : g.gate ∈ CliffordT then
        .gate ⟨g.gate, hg, g.wires.trans (s3_dataWireEmb n r b)⟩
          (s3_compileA resetFalse resetTrue half1 half2 n r b hb hr next f bank)
      else
        have hgrid : ∃ j : ℕ, j < (s3_B b) ^ r ∧
            g.gate = Gate.ofMatrix1 (rot (2 * Real.pi * (j : ℝ) / (((s3_B b) ^ r : ℕ) : ℝ))) := by
          rcases g.mem with h | h
          · exact False.elim (hg h)
          · exact h
        let j := Classical.choose hgrid
        have hj := Classical.choose_spec hgrid
        let har : g.gate.arity = 1 := congrArg Gate.arity hj.2
        let q : Fin n := g.wires (Fin.cast har.symm 0)
        s3_compileRotList resetFalse resetTrue half1 half2 n r b hb hr j q (List.finRange r)
          f bank (fun f' bank' =>
            s3_compileA resetFalse resetTrue half1 half2 n r b hb hr next f' bank')

private theorem s3_compileA_maxGates
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hrF : resetFalse.size ≤ 1) (hrT : resetTrue.size ≤ 5)
    (hh1 : half1.size ≤ 38) (hh2 : half2.size ≤ 36)
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) :
    ∀ (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n)
      (f : ℕ) (bank : s3_Bank r b),
      (s3_compileA resetFalse resetTrue half1 half2 n r b hb hr A f bank).maxGates ≤
        A.maxGates + 74 * s3_pot f bank
  | .done, f, bank => by
      simp [s3_compileA, AdaptiveCircuit.maxGates]
  | .measure q next, f, bank => by
      simp only [s3_compileA, AdaptiveCircuit.maxGates]
      have ihf := s3_compileA_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
        n r b hb hr (next false) f bank
      have iht := s3_compileA_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
        n r b hb hr (next true) f bank
      exact max_le (le_trans ihf (Nat.add_le_add_right (le_max_left _ _) _))
        (le_trans iht (Nat.add_le_add_right (le_max_right _ _) _))
  | .gate g next, f, bank => by
      dsimp only [s3_compileA, AdaptiveCircuit.maxGates]
      split_ifs with hg
      · simp only [AdaptiveCircuit.maxGates]
        have ih := s3_compileA_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
          n r b hb hr next f bank
        omega
      · refine le_trans
          (s3_compileRotList_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
            n r b hb hr _ _ (List.finRange r) f bank _ next.maxGates
            (fun f' b' => s3_compileA_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
              n r b hb hr next f' b')) ?_
        omega

private theorem s3_compileA_close (s1 : Thm9Step1API) (s2 : Thm9Step2API)
    (resetFalse resetTrue : Circuit CliffordT 1)
    (half1 half2 : Circuit CliffordT 4)
    (hstep :
      ∀ (N m_ref : ℕ) (w_targ w_bank : Fin N) (hne : w_targ ≠ w_bank) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire w_bank (resourceVec θ) σ →
        let w1_bank : Fin 1 ↪ Fin N := ⟨fun _ => w_bank, fun i j _ => Subsingleton.elim i j⟩
        let g_cnot := cnotApp t9_cnot_mem_cliffordT w_targ w_bank hne
        let σ_cnot := t9_unitConj (embedOp g_cnot.gate.mat g_cnot.wires) σ
        let P (b : Bool) := AdaptiveCircuit.proj w_bank b
        t9_unitConj (embedOp resetFalse.unitary w1_bank) (t9_unitConj (P false) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire θ w_targ) (t9_traceAndSetWire w_bank plusVec σ) ∧
        t9_unitConj (embedOp resetTrue.unitary w1_bank) (t9_unitConj (P true) σ_cnot) =
          ((1 / 2 : ℝ) : ℂ) •
            t9_unitConj (t9_rotOnWire (-θ) w_targ) (t9_traceAndSetWire w_bank plusVec σ))
    (hsplit :
      ∀ (N m_ref : ℕ) (w : Fin 4 ↪ Fin N) (θ : ℝ)
        (σ : Matrix (Fin m_ref × Qubits N) (Fin m_ref × Qubits N) ℂ),
        t9_HasPureWire (w 0) (resourceVec θ) σ →
        t9_HasPureWire (w 2) plusVec σ →
        t9_HasPureWire (w 3) (basisVec false) σ →
        t9_unitConj (embedOp half2.unitary w)
          (t9_unitConj (t9_rotOnWire (2 * θ) (w 3))
            (t9_unitConj (embedOp half1.unitary w) σ)) =
          t9_unitConj (t9_rotOnWire θ (w 1))
            (t9_traceAndSetWire (w 2) (resourceVec θ) σ))
    (n r b : ℕ) (hb : 1 ≤ b) (hr : 2 ≤ r) :
    ∀ (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n)
      (f : ℕ) (bank : s3_Bank r b) (m_ref : ℕ)
      (σ : Matrix (Fin m_ref × Qubits (s3_N n r b)) (Fin m_ref × Qubits (s3_N n r b)) ℂ),
      WildeQIT.IsDensityOperator σ →
      s3_HasAncStateLe n r b (s3_M b r - 1) bank σ →
      WildeQIT.traceDist
        (t9_partialTraceAnc ((s3_compileA resetFalse resetTrue half1 half2 n r b hb hr A f bank).channelRef m_ref σ))
        (A.channelRef m_ref (t9_partialTraceAnc σ)) ≤
        s3_binomErr f (r * A.maxGates)
  | .done, f, bank, m_ref, σ, hσ, _ => by
      have hdone :
          t9_partialTraceAnc
            (((s3_compileA resetFalse resetTrue half1 half2 n r b hb hr .done f bank).channelRef m_ref σ)) =
          (.done : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n).channelRef m_ref
            (t9_partialTraceAnc σ) := by
        simp [s3_compileA, AdaptiveCircuit.channelRef, AdaptiveCircuit.krausList]
      rw [hdone, s1.traceDist_self]
      exact s3_binomErr_nonneg f _
  | .gate g next, f, bank, m_ref, σ, hσ, hanc => by
      dsimp only [s3_compileA]
      split_ifs with hg
      · rw [s3_channelRef_gate, s3_channelRef_gate]
        let g' : GateApp CliffordT (s3_N n r b) := ⟨g.gate, hg, g.wires.trans (s3_dataWireEmb n r b)⟩
        let σ' := t9_unitConj (embedOp g'.gate.mat g'.wires) σ
        have hU : embedOp g'.gate.mat g'.wires ∈ Matrix.unitaryGroup (Qubits (s3_N n r b)) ℂ :=
          s3_embedOp_isUnitary (s1.cliffordT_isUnitary g.gate hg) g'.wires
        have hσ'_dens : WildeQIT.IsDensityOperator σ' :=
          s3_isDensityOperator_unitConj s1 hU hσ
        have hanc' : s3_HasAncStateLe n r b (s3_M b r - 1) bank σ' :=
          s3_HasAncStateLe_unitConj_data s2 g.gate.mat g.wires hanc
        have hpt' :
            t9_partialTraceAnc σ' =
            t9_unitConj (embedOp g.gate.mat g.wires) (t9_partialTraceAnc σ) :=
          s3_partialTraceAnc_unitConj_embedOp_data g.gate.mat g.wires σ
        have ih := s3_compileA_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
          n r b hb hr next f bank m_ref σ' hσ'_dens hanc'
        rw [hpt'] at ih
        refine le_trans ih (s3_binomErr_mono_right f ?_)
        simp only [AdaptiveCircuit.maxGates]
        exact Nat.mul_le_mul_left r (Nat.le_add_left next.maxGates 1)
      · have hgrid : ∃ j : ℕ, j < (s3_B b) ^ r ∧
            g.gate = Gate.ofMatrix1 (rot (2 * Real.pi * (j : ℝ) / (((s3_B b) ^ r : ℕ) : ℝ))) := by
          rcases g.mem with h | h
          · exact False.elim (hg h)
          · exact h
        let j := Classical.choose hgrid
        have hj := Classical.choose_spec hgrid
        let har : g.gate.arity = 1 := congrArg Gate.arity hj.2
        let q : Fin n := g.wires (Fin.cast har.symm 0)
        have hg_op : embedOp g.gate.mat g.wires =
            t9_rotOnWire (2 * Real.pi * (j : ℝ) / (((s3_B b) ^ r : ℕ) : ℝ)) q := by
          rw [s3_embedOp_of_gate_eq hj.2 g.wires (s3_w1 q) (fun i => by rw [Fin.eq_zero i]; rfl)]
          rfl
        have hang_sum :
            2 * Real.pi * (j : ℝ) / (((s3_B b) ^ r : ℕ) : ℝ) =
            s3_sumAngles b r j (List.finRange r) := by
          rw [s3_grid_angle_eq_sum b r hb j hj.1]
          dsimp only [s3_sumAngles]
          rw [Fin.sum_univ_def]
        have hg_op_sum : embedOp g.gate.mat g.wires =
            t9_rotOnWire (s3_sumAngles b r j (List.finRange r)) q := by
          rw [hg_op, hang_sum]
        have hρ_dens : WildeQIT.IsDensityOperator (t9_partialTraceAnc σ) :=
          s1.isDensityOperator_partialTraceAnc hσ
        have htarg_dens : WildeQIT.IsDensityOperator
            ((AdaptiveCircuit.gate g next).channelRef m_ref (t9_partialTraceAnc σ)) :=
          s3_isDensityOperator_channelRef
            (s3_cliffordT_union_gridGates_isUnitary s1 ((2 ^ b) ^ r))
            (.gate g next) hρ_dens
        have hlen : (List.finRange r).length = r := List.length_finRange
        have hmax_eq : r * (AdaptiveCircuit.gate g next).maxGates = r * next.maxGates + (List.finRange r).length := by
          simp [AdaptiveCircuit.maxGates, hlen]
          ring
        rw [hmax_eq]
        refine s3_compileRotList_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
          n r b hb hr j q (List.finRange r) f bank _ m_ref σ _ (r * next.maxGates)
          hσ hanc htarg_dens ?_
        intro f' _ bank' σ_end hσ_end_dens hanc_end hpt_end
        have hch_eq :
            (AdaptiveCircuit.gate g next).channelRef m_ref (t9_partialTraceAnc σ) =
            next.channelRef m_ref (t9_partialTraceAnc σ_end) := by
          rw [s3_channelRef_gate, hpt_end, hg_op_sum]
        rw [hch_eq]
        exact s3_compileA_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
          n r b hb hr next f' bank' m_ref σ_end hσ_end_dens hanc_end
  | .measure q next, f, bank, m_ref, σ, hσ, hanc => by
      dsimp only [s3_compileA]
      rw [s3_channelRef_measure, s3_channelRef_measure]
      rcases s1.proj_decomp_density (s3_dataWire n r b q) hσ with
        ⟨pf, pt, σf, σt, hpf0, hpt0, hpft, hσf, hσt, hdecf, hdect⟩
      change t9_unitConj (AdaptiveCircuit.proj (s3_dataWire n r b q) false) σ = (pf : ℂ) • σf at hdecf
      change t9_unitConj (AdaptiveCircuit.proj (s3_dataWire n r b q) true) σ = (pt : ℂ) • σt at hdect
      rw [hdecf, hdect, s3_channelRef_smul, s3_channelRef_smul,
        s3_partialTraceAnc_add, s3_partialTraceAnc_smul, s3_partialTraceAnc_smul]
      have hptf :
          t9_unitConj (AdaptiveCircuit.proj q false) (t9_partialTraceAnc σ) =
          (pf : ℂ) • t9_partialTraceAnc σf := by
        rw [← s3_partialTraceAnc_unitConj_proj_data q false σ]
        change t9_partialTraceAnc (t9_unitConj (AdaptiveCircuit.proj (s3_dataWire n r b q) false) σ) = _
        rw [hdecf, s3_partialTraceAnc_smul]
      have hptt :
          t9_unitConj (AdaptiveCircuit.proj q true) (t9_partialTraceAnc σ) =
          (pt : ℂ) • t9_partialTraceAnc σt := by
        rw [← s3_partialTraceAnc_unitConj_proj_data q true σ]
        change t9_partialTraceAnc (t9_unitConj (AdaptiveCircuit.proj (s3_dataWire n r b q) true) σ) = _
        rw [hdect, s3_partialTraceAnc_smul]
      rw [hptf, hptt, s3_channelRef_smul, s3_channelRef_smul]
      let cf := s3_compileA resetFalse resetTrue half1 half2 n r b hb hr (next false) f bank
      let ct := s3_compileA resetFalse resetTrue half1 half2 n r b hb hr (next true) f bank
      have hsub :
          (((pf : ℂ) • t9_partialTraceAnc (cf.channelRef m_ref σf) +
            (pt : ℂ) • t9_partialTraceAnc (ct.channelRef m_ref σt)) -
           ((pf : ℂ) • (next false).channelRef m_ref (t9_partialTraceAnc σf) +
            (pt : ℂ) • (next true).channelRef m_ref (t9_partialTraceAnc σt))) =
          (pf : ℂ) • (t9_partialTraceAnc (cf.channelRef m_ref σf) -
            (next false).channelRef m_ref (t9_partialTraceAnc σf)) +
          (pt : ℂ) • (t9_partialTraceAnc (ct.channelRef m_ref σt) -
            (next true).channelRef m_ref (t9_partialTraceAnc σt)) := by
        simp only [smul_sub]
        abel
      have hHermf :
          (t9_partialTraceAnc (cf.channelRef m_ref σf) -
            (next false).channelRef m_ref (t9_partialTraceAnc σf)).IsHermitian :=
        (s1.isHermitian_partialTraceAnc (s1.isHermitian_channelRef _ hσf.1.isHermitian)).sub
          (s1.isHermitian_channelRef _ (s1.isDensityOperator_partialTraceAnc hσf).1.isHermitian)
      have hHermt :
          (t9_partialTraceAnc (ct.channelRef m_ref σt) -
            (next true).channelRef m_ref (t9_partialTraceAnc σt)).IsHermitian :=
        (s1.isHermitian_partialTraceAnc (s1.isHermitian_channelRef _ hσt.1.isHermitian)).sub
          (s1.isHermitian_channelRef _ (s1.isDensityOperator_partialTraceAnc hσt).1.isHermitian)
      have htermf :
          pf * WildeQIT.traceNorm
            (t9_partialTraceAnc (cf.channelRef m_ref σf) -
              (next false).channelRef m_ref (t9_partialTraceAnc σf)) ≤
          pf * s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) := by
        by_cases hpf_zero : pf = 0
        · rw [hpf_zero]; simp
        · have hancf := s3_HasAncStateLe_of_proj_smul s2 q false hpf_zero hanc hdecf
          have ihf := s3_compileA_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
            n r b hb hr (next false) f bank m_ref σf hσf hancf
          have hmono := s3_binomErr_mono_right f
            (Nat.mul_le_mul_left r (le_max_left (next false).maxGates (next true).maxGates))
          exact mul_le_mul_of_nonneg_left (le_trans ihf hmono) hpf0
      have htermt :
          pt * WildeQIT.traceNorm
            (t9_partialTraceAnc (ct.channelRef m_ref σt) -
              (next true).channelRef m_ref (t9_partialTraceAnc σt)) ≤
          pt * s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) := by
        by_cases hpt_zero : pt = 0
        · rw [hpt_zero]; simp
        · have hanct := s3_HasAncStateLe_of_proj_smul s2 q true hpt_zero hanc hdect
          have iht := s3_compileA_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
            n r b hb hr (next true) f bank m_ref σt hσt hanct
          have hmono := s3_binomErr_mono_right f
            (Nat.mul_le_mul_left r (le_max_right (next false).maxGates (next true).maxGates))
          exact mul_le_mul_of_nonneg_left (le_trans iht hmono) hpt0
      rw [WildeQIT.traceDist, hsub]
      have hadd := s1.traceNorm_add_le
        (s3_isHermitian_real_smul pf hHermf) (s3_isHermitian_real_smul pt hHermt)
      rw [s1.traceNorm_smul_of_nonneg hpf0 hHermf, s1.traceNorm_smul_of_nonneg hpt0 hHermt] at hadd
      calc WildeQIT.traceNorm
            ((pf : ℂ) • (t9_partialTraceAnc (cf.channelRef m_ref σf) -
                (next false).channelRef m_ref (t9_partialTraceAnc σf)) +
              (pt : ℂ) • (t9_partialTraceAnc (ct.channelRef m_ref σt) -
                (next true).channelRef m_ref (t9_partialTraceAnc σt)))
          ≤ pf * WildeQIT.traceNorm
              (t9_partialTraceAnc (cf.channelRef m_ref σf) -
                (next false).channelRef m_ref (t9_partialTraceAnc σf)) +
            pt * WildeQIT.traceNorm
              (t9_partialTraceAnc (ct.channelRef m_ref σt) -
                (next true).channelRef m_ref (t9_partialTraceAnc σt)) := hadd
        _ ≤ pf * s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) +
            pt * s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) :=
            add_le_add htermf htermt
        _ = (pf + pt) * s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) := by ring
        _ = s3_binomErr f (r * (AdaptiveCircuit.measure q next).maxGates) := by rw [hpft, one_mul]

private theorem s3_step3_main (s1 : Thm9Step1API) (s2 : Thm9Step2API) :
    ∀ (r b : ℕ), 2 ≤ r → 1 ≤ b → ∀ (m_cut n G : ℕ)
      (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n),
      A.maxGates ≤ G →
      let L : ℕ := 2 * (2 ^ b * (b * r))
      let M : ℕ := b * r
      ∃ (α : Fin L → ℝ)
        (B_circ : AdaptiveCircuit CliffordT (n + (L + M))),
        (B_circ.maxGates : ℝ) ≤ (G : ℝ) + 200 * (m_cut : ℝ) ∧
        ∀ (m_ref : ℕ)
          (ρ : Matrix (Fin m_ref × Qubits n) (Fin m_ref × Qubits n) ℂ),
          WildeQIT.IsDensityOperator ρ →
          WildeQIT.traceDist
            (t9_partialTraceAnc
              (B_circ.channelRef m_ref (t9_tensorAncVec (t9_productAncVec α) ρ)))
            (A.channelRef m_ref ρ) ≤
            2 * ((∑ k ∈ Finset.range (r * G), (m_cut.choose k : ℝ)) / 2 ^ m_cut) := by
  intro r b hr hb m_cut n G A hAG
  rcases s2.stateInjection_step with ⟨resetFalse, resetTrue, hrF, hrT, hstep⟩
  rcases s2.phaseHalving_split with ⟨half1, half2, hh1, hh2, hsplit⟩
  let α := s3_α r b hb hr
  let bank₀ : s3_Bank r b := fun _ => true
  let B_circ := s3_compileA resetFalse resetTrue half1 half2 n r b hb hr A m_cut bank₀
  refine ⟨α, B_circ, ?_, ?_⟩
  · have hpot0 : s3_pot m_cut bank₀ = 2 * m_cut := by
      have hemp : s3_emptyCount bank₀ = 0 := by
        simp [s3_emptyCount, bank₀]
      simp [s3_pot, hemp]
    have hmax := s3_compileA_maxGates resetFalse resetTrue half1 half2 hrF hrT hh1 hh2
      n r b hb hr A m_cut bank₀
    rw [hpot0] at hmax
    have hnat : (s3_compileA resetFalse resetTrue half1 half2 n r b hb hr A m_cut bank₀).maxGates ≤
        G + 200 * m_cut := by omega
    exact_mod_cast hnat
  · intro m_ref ρ hρ
    have hnorm := s3_norm_sq_productAncVec s2 (M := s3_M b r) α
    have hσ_dens : WildeQIT.IsDensityOperator
        (t9_tensorAncVec (t9_productAncVec α) ρ) :=
      s1.isDensityOperator_tensorAncVec hnorm hρ
    have hanc₀ : s3_HasAncStateLe n r b (s3_M b r - 1) bank₀
        (t9_tensorAncVec (t9_productAncVec α) ρ) :=
      s3_HasAncStateLe_init s2 n r b hb hr ρ
    have hclose := s3_compileA_close s1 s2 resetFalse resetTrue half1 half2 hstep hsplit
      n r b hb hr A m_cut bank₀ m_ref (t9_tensorAncVec (t9_productAncVec α) ρ) hσ_dens hanc₀
    rw [s3_partialTraceAnc_tensorAncVec hnorm ρ] at hclose
    exact le_trans hclose (s3_binomErr_mono_right m_cut (Nat.mul_le_mul_left r hAG))

end Thm9Step3Helpers

theorem t9_step3 : Thm9Step3Type := by
  intro s1 s2
  exact ⟨s3_step3_b0 s1 s2, s3_step3_G0 s1, s3_step3_main s1 s2⟩

section Thm9Step4Helpers

private lemma t9_step4_log_pow2_ge {b : ℕ} (hb : 1 ≤ b) :
    Real.log 2 ≤ Real.log ((2 : ℝ) ^ b) := by
  rw [Real.log_pow]
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Real.log 2 = 1 * Real.log 2 := (one_mul _).symm
    _ ≤ (b : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hb1 hlog2_pos.le

private lemma t9_step4_base_lower {r b : ℕ} (hr : 2 ≤ r) (hb : 1 ≤ b) :
    (277 / 100 : ℝ) < (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h2b_le : (2 : ℝ) ≤ (2 : ℝ) ^ b := by
    have hpow : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have hpow_r : ((2 ^ 1 : ℕ) : ℝ) ≤ ((2 ^ b : ℕ) : ℝ) := by exact_mod_cast hpow
    simpa using hpow_r
  have hlog_ge : (0.6931471803 : ℝ) < Real.log ((2 : ℝ) ^ b) :=
    lt_of_lt_of_le Real.log_two_gt_d9 (t9_step4_log_pow2_ge hb)
  have hprod4 : (4 : ℝ) ≤ (r : ℝ) * (2 : ℝ) ^ b :=
    by nlinarith only [hr2, h2b_le]
  nlinarith only [hprod4, hlog_ge]

private lemma t9_step4_one_lt_log_Z {r b : ℕ} (hr : 2 ≤ r) (hb : 1 ≤ b)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    1 < Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)) := by
  have hbase : (277 / 100 : ℝ) < (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) :=
    t9_step4_base_lower hr hb
  have hε_inv : 1 ≤ ε⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hε0]
    linarith only [hε1]
  have hZ_ge : (277 / 100 : ℝ) < ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b) := by
    have hbase_nonneg : 0 ≤ (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) := by
      linarith only [hbase]
    have hmul : (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) ≤
        ε⁻¹ * ((r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hε_inv hbase_nonneg
    linarith only [hbase, hmul]
  have hexp_lt : Real.exp 1 < ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b) :=
    lt_trans Real.exp_one_lt_d9 (by linarith only [hZ_ge])
  have hlog_lt := Real.log_lt_log (Real.exp_pos 1) hexp_lt
  simpa [Real.log_exp] using hlog_lt

end Thm9Step4Helpers

theorem t9_step4 : Thm9Step4Type := by
  intro C_RS ε₀ hC_RS hε₀
  let K_eps : ℝ := max 0 (Real.log (2 / ε₀))
  let C₀ : ℝ := max 801 (4 * C_RS * (K_eps + 33) + 3400)
  have hK_nonneg : 0 ≤ K_eps := le_max_left 0 _
  have hK_ge : Real.log (2 / ε₀) ≤ K_eps := le_max_right 0 _
  have hC₀_801 : 801 ≤ C₀ := le_max_left 801 _
  have hC₀_1 : 1 ≤ C₀ := by linarith only [hC₀_801]
  have hC₀_nonneg : 0 ≤ C₀ := by linarith only [hC₀_801]
  have hC₀_T2 : 4 * C_RS * (K_eps + 33) + 3400 ≤ C₀ := le_max_right 801 _
  refine ⟨C₀, ?_, ?_, ?_⟩
  · -- Conjunct 1: b = 0
    intro r hr ε G
    have hlog1 : Real.log ((2 : ℝ) ^ (0 : ℕ)) = 0 := by simp
    rw [hlog1]
    have hhr : (1 : ℝ) ≤ (r : ℝ) := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith only [hr2]
    have hG_nonneg : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
    have hrG : (G : ℝ) ≤ (r : ℝ) * (G : ℝ) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hhr hG_nonneg
    have hrG_nonneg : 0 ≤ (r : ℝ) * (G : ℝ) := by positivity
    calc
      (G : ℝ) ≤ (r : ℝ) * (G : ℝ) := hrG
      _ = 1 * ((r : ℝ) * (G : ℝ)) := (one_mul _).symm
      _ ≤ C₀ * ((r : ℝ) * (G : ℝ)) := mul_le_mul_of_nonneg_right hC₀_1 hrG_nonneg
      _ = C₀ * ((r : ℝ) * (G : ℝ) +
            (r : ℝ) * (2 : ℝ) ^ (0 : ℕ) * 0 *
              Real.log (ε⁻¹ * (2 : ℝ) ^ (0 : ℕ) * (r : ℝ) * 0)) := by ring
  · -- Conjunct 2: G = 0
    intro r b hr hb ε hε0 hε1
    have hP_pos : 0 < (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) := by
      linarith only [t9_step4_base_lower hr hb]
    have hlogZ_pos : 0 < Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)) := by
      linarith only [t9_step4_one_lt_log_Z hr hb hε0 hε1]
    have hcast0 : ((0 : ℕ) : ℝ) = 0 := by simp
    rw [hcast0]
    positivity
  · -- Conjunct 3: Main bound (2 ≤ r, 1 ≤ b, 0 < ε ≤ 1, 1 ≤ G)
    intro r b hr hb ε hε0 hε1 G hG
    dsimp only
    let L : ℕ := 2 * (2 ^ b * (b * r))
    let δ_tot : ℝ := ε / 4
    let m_cut : ℕ := max (4 * (r * G)) (Nat.ceil (8 * Real.log (4 / ε)))
    refine ⟨m_cut, δ_tot, by positivity, ?_, ?_⟩
    · -- Error sum bound
      have h4rG : 4 * (r * G) ≤ m_cut := le_max_left _ _
      have hbin := ConstOverheadCompile.Main.binomial_tail_eq16 (r * G) m_cut h4rG
      have hceil_le : Nat.ceil (8 * Real.log (4 / ε)) ≤ m_cut := le_max_right _ _
      have hm_ge : 8 * Real.log (4 / ε) ≤ (m_cut : ℝ) := by
        have h1 : 8 * Real.log (4 / ε) ≤ (Nat.ceil (8 * Real.log (4 / ε)) : ℝ) :=
          Nat.le_ceil _
        have h2 : ((Nat.ceil (8 * Real.log (4 / ε)) : ℕ) : ℝ) ≤ (m_cut : ℝ) := by
          exact_mod_cast hceil_le
        linarith only [h1, h2]
      have hexp_le : Real.exp (-(m_cut : ℝ) / 8) ≤ ε / 4 := by
        have hneg : -(m_cut : ℝ) / 8 ≤ -Real.log (4 / ε) := by linarith only [hm_ge]
        have hexp_mono : Real.exp (-(m_cut : ℝ) / 8) ≤ Real.exp (-Real.log (4 / ε)) :=
          Real.exp_le_exp.mpr hneg
        have h4ε_pos : 0 < 4 / ε := by positivity
        have hexp_eq : Real.exp (-Real.log (4 / ε)) = ε / 4 := by
          rw [Real.exp_neg, Real.exp_log h4ε_pos, inv_div]
        linarith only [hexp_mono, hexp_eq]
      have hδ_eq : δ_tot = ε / 4 := rfl
      linarith only [hbin, hexp_le, hδ_eq]
    · -- Gate sum bound
      let P : ℝ := (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b)
      let Z : ℝ := ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)
      let T₁ : ℝ := (r : ℝ) * (G : ℝ)
      let T₂ : ℝ := P * Real.log Z
      have hP_gt : (277 / 100 : ℝ) < P := t9_step4_base_lower hr hb
      have hP_ge2 : 2 ≤ P := by linarith only [hP_gt]
      have hP_ge1 : 1 ≤ P := by linarith only [hP_gt]
      have hP_pos : 0 < P := by linarith only [hP_gt]
      have hlogZ_gt1 : 1 < Real.log Z := t9_step4_one_lt_log_Z hr hb hε0 hε1
      have hlogZ_ge1 : 1 ≤ Real.log Z := le_of_lt hlogZ_gt1
      have hlogZ_pos : 0 < Real.log Z := by linarith only [hlogZ_gt1]
      have hlogZ_le_T₂ : Real.log Z ≤ T₂ := by
        calc
          Real.log Z = 1 * Real.log Z := (one_mul _).symm
          _ ≤ P * Real.log Z := mul_le_mul_of_nonneg_right hP_ge1 hlogZ_pos.le
      have h1_le_T₂ : 1 ≤ T₂ := le_trans hlogZ_ge1 hlogZ_le_T₂
      have hT₁_nonneg : 0 ≤ T₁ := by positivity
      have hT₂_nonneg : 0 ≤ T₂ := by positivity
      have hZ_eq : Z = ε⁻¹ * P := by dsimp only [Z, P]; ring
      have hZ_pos : 0 < Z := by rw [hZ_eq]; positivity
      have hlog2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
        linarith only [Real.log_two_gt_d9]
      have hlog2_pos : 0 < Real.log 2 := by linarith only [hlog2_gt_half]
      have hL_eq : (L : ℝ) = (2 / Real.log 2) * P := by
        have hL_cast : (L : ℝ) = 2 * ((2 : ℝ) ^ b * ((b : ℝ) * (r : ℝ))) := by
          dsimp only [L]
          push_cast
          ring
        have hlog_pow : Real.log ((2 : ℝ) ^ b) = (b : ℝ) * Real.log 2 := Real.log_pow 2 b
        rw [hL_cast]
        dsimp only [P]
        rw [hlog_pow]
        field_simp [hlog2_pos.ne']
      have hL_le : (L : ℝ) ≤ 4 * P := by
        have hcoef : 2 / Real.log 2 ≤ 4 := by
          rw [div_le_iff₀ hlog2_pos]
          linarith only [hlog2_gt_half]
        rw [hL_eq]
        exact mul_le_mul_of_nonneg_right hcoef hP_pos.le
      have hL_nonneg : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
      have h2Lδ_eq : 2 * (L : ℝ) / δ_tot = (16 / Real.log 2) * Z := by
        have hδ_eq : δ_tot = ε / 4 := rfl
        rw [hδ_eq, hL_eq, hZ_eq]
        field_simp [hε0.ne', hlog2_pos.ne']
        ring
      have h2Lδ_le : 2 * (L : ℝ) / δ_tot ≤ 32 * Z := by
        have hcoef : 16 / Real.log 2 ≤ 32 := by
          rw [div_le_iff₀ hlog2_pos]
          linarith only [hlog2_gt_half]
        rw [h2Lδ_eq]
        exact mul_le_mul_of_nonneg_right hcoef hZ_pos.le
      have h2Lδ_pos : 0 < 2 * (L : ℝ) / δ_tot := by
        rw [h2Lδ_eq]
        have : 0 < 16 / Real.log 2 := by positivity
        positivity
      have hlog_max_le :
          Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot)) ≤ (K_eps + 33) * Real.log Z := by
        rcases le_total (2 / ε₀) (2 * (L : ℝ) / δ_tot) with hle | hle
        · rw [max_eq_right hle]
          have hlog32Z : Real.log (2 * (L : ℝ) / δ_tot) ≤ Real.log (32 * Z) :=
            Real.log_le_log h2Lδ_pos h2Lδ_le
          have hlog32_split : Real.log (32 * Z) = Real.log 32 + Real.log Z :=
            Real.log_mul (by norm_num) hZ_pos.ne'
          have hlog32_le : Real.log 32 ≤ 32 := by
            linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 32)]
          have h1 : Real.log 32 + Real.log Z ≤ 33 * Real.log Z := by
            nlinarith only [hlog32_le, hlogZ_ge1]
          have h2 : 33 * Real.log Z ≤ (K_eps + 33) * Real.log Z := by
            nlinarith only [hK_nonneg, hlogZ_pos]
          linarith only [hlog32Z, hlog32_split, h1, h2]
        · rw [max_eq_left hle]
          have h1 : Real.log (2 / ε₀) ≤ K_eps := hK_ge
          have h2 : K_eps ≤ K_eps * Real.log Z := by
            nlinarith only [hK_nonneg, hlogZ_ge1]
          have h3 : K_eps * Real.log Z ≤ (K_eps + 33) * Real.log Z := by
            nlinarith only [hlogZ_pos]
          linarith only [h1, h2, h3, hlogZ_ge1]
      have hterm1 :
          (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) ≤
            4 * C_RS * (K_eps + 33) * T₂ := by
        have hstep1 :
            C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot)) ≤
              C_RS * ((K_eps + 33) * Real.log Z) :=
          mul_le_mul_of_nonneg_left hlog_max_le hC_RS.le
        have hstep2 :
            (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) ≤
              (L : ℝ) * (C_RS * ((K_eps + 33) * Real.log Z)) :=
          mul_le_mul_of_nonneg_left hstep1 hL_nonneg
        have hrhs_nonneg : 0 ≤ C_RS * ((K_eps + 33) * Real.log Z) := by positivity
        have hstep3 :
            (L : ℝ) * (C_RS * ((K_eps + 33) * Real.log Z)) ≤
              (4 * P) * (C_RS * ((K_eps + 33) * Real.log Z)) :=
          mul_le_mul_of_nonneg_right hL_le hrhs_nonneg
        have hring : (4 * P) * (C_RS * ((K_eps + 33) * Real.log Z)) =
            4 * C_RS * (K_eps + 33) * T₂ := by
          dsimp only [T₂]
          ring
        linarith only [hstep2, hstep3, hring]
      have hG_le : (G : ℝ) ≤ T₁ := by
        have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
          have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
          linarith only [hr2]
        have hG_nonneg : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
        dsimp only [T₁]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hG_nonneg
      have hm_cut_le : (m_cut : ℝ) ≤ 4 * T₁ + 17 * T₂ := by
        have hm_nat : m_cut ≤ 4 * (r * G) + Nat.ceil (8 * Real.log (4 / ε)) := by
          dsimp only [m_cut]
          omega
        have hm_real : (m_cut : ℝ) ≤ 4 * ((r : ℝ) * (G : ℝ)) +
            (Nat.ceil (8 * Real.log (4 / ε)) : ℝ) := by
          have h := (Nat.cast_le (α := ℝ)).mpr hm_nat
          push_cast at h
          linarith only [h]
        have h4ε_gt1 : 1 < 4 / ε := by
          rw [one_lt_div hε0]
          linarith only [hε1]
        have h8log_nonneg : 0 ≤ 8 * Real.log (4 / ε) := by
          have hpos := Real.log_pos h4ε_gt1
          linarith only [hpos]
        have hceil_ub : (Nat.ceil (8 * Real.log (4 / ε)) : ℝ) ≤ 8 * Real.log (4 / ε) + 1 :=
          (Nat.ceil_lt_add_one h8log_nonneg).le
        have h4ε_le_2Z : 4 / ε ≤ 2 * Z := by
          have hε_inv_pos : 0 < ε⁻¹ := inv_pos.mpr hε0
          have h1 : 2 * ε⁻¹ ≤ P * ε⁻¹ := mul_le_mul_of_nonneg_right hP_ge2 hε_inv_pos.le
          have h2 : 4 / ε = 2 * (2 * ε⁻¹) := by ring
          rw [h2, hZ_eq]
          linarith only [h1]
        have hlog4ε_le : Real.log (4 / ε) ≤ 2 * Real.log Z := by
          have h4ε_pos : 0 < 4 / ε := by positivity
          have h1 : Real.log (4 / ε) ≤ Real.log (2 * Z) := Real.log_le_log h4ε_pos h4ε_le_2Z
          have h2 : Real.log (2 * Z) = Real.log 2 + Real.log Z :=
            Real.log_mul (by norm_num) hZ_pos.ne'
          have h3 : Real.log 2 ≤ 1 := by
            linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
          linarith only [h1, h2, h3, hlogZ_ge1]
        have hT₁_eq : T₁ = (r : ℝ) * (G : ℝ) := rfl
        linarith only [hm_real, hceil_ub, hlog4ε_le, hlogZ_le_T₂, h1_le_T₂, hT₁_eq]
      have hLHS_le :
          (L : ℝ) * (C_RS * Real.log (max (2 / ε₀) (2 * (L : ℝ) / δ_tot))) +
            (G : ℝ) + 200 * (m_cut : ℝ) ≤
              801 * T₁ + (4 * C_RS * (K_eps + 33) + 3400) * T₂ := by
        linarith only [hterm1, hG_le, hm_cut_le]
      have hRHS_ge :
          801 * T₁ + (4 * C_RS * (K_eps + 33) + 3400) * T₂ ≤ C₀ * (T₁ + T₂) := by
        have h1 : 801 * T₁ ≤ C₀ * T₁ := mul_le_mul_of_nonneg_right hC₀_801 hT₁_nonneg
        have h2 : (4 * C_RS * (K_eps + 33) + 3400) * T₂ ≤ C₀ * T₂ :=
          mul_le_mul_of_nonneg_right hC₀_T2 hT₂_nonneg
        linarith only [h1, h2]
      have hT_eq : T₁ + T₂ = (r : ℝ) * (G : ℝ) +
          (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
            Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b)) := rfl
      rw [← hT_eq]
      exact le_trans hLHS_le hRHS_ge

theorem solution :
    ∃ C₀ : ℝ, ∀ r b : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (n G : ℕ)
        (A : ConstOverheadCompile.Main.AdaptiveCircuit
          (ConstOverheadCompile.Main.CliffordT ∪ ConstOverheadCompile.Main.gridGates ((2 ^ b) ^ r)) n),
        A.maxGates ≤ G →
        ∃ (a : ℕ)
          (A' : ConstOverheadCompile.Main.AdaptiveCircuit ConstOverheadCompile.Main.CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C₀ * ((r : ℝ) * G + (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
              Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b))) ∧
          ConstOverheadCompile.Main.DiamondClose A'.dataChannelRef A.channelRef ε :=
  t9_master_glue_check t9_step1_api t9_step2_api t9_step3 t9_step4
