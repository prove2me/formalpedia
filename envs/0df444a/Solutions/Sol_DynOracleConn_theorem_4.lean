-- Prove2me | solution 1 for DynOracleConn.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:43:26.896842+00:00
-- url     : https://prove2.me/submissions/ac31a0cf-bc9c-49fc-969a-eb2bd04908fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DynOracleConn_Oracles
import Definitions.Def_DynOracleConn_RandAlg
import Theorems.Thm_DynOracleConn_corollary_3_3
import Theorems.Thm_DynOracleConn_corollary_3_6
import Theorems.Thm_DynOracleConn_theorem_3_7
import Theorems.Thm_DynOracleConn_reduction
import Theorems.Thm_DynOracleConn_list_to_matrix

open DynOracleConn MeasureTheory

namespace AuxThm4

def gvIdx {d : ℕ} : GV d → Fin (2 + 8 * d)
  | .s => ⟨0, by omega⟩
  | .t => ⟨1, by omega⟩
  | .l false j => ⟨2 + 8 * j.val, by omega⟩
  | .l true j => ⟨3 + 8 * j.val, by omega⟩
  | .r false j => ⟨4 + 8 * j.val, by omega⟩
  | .r true j => ⟨5 + 8 * j.val, by omega⟩
  | .u false i => ⟨6 + 8 * i.val, by omega⟩
  | .u true i => ⟨7 + 8 * i.val, by omega⟩
  | .v false i => ⟨8 + 8 * i.val, by omega⟩
  | .v true i => ⟨9 + 8 * i.val, by omega⟩

def gvInv {d : ℕ} (m : Fin (2 + 8 * d)) : GV d :=
  if h : m.val < 2 then
    if m.val = 0 then .s else .t
  else
    let k : Fin d := ⟨(m.val - 2) / 8, by omega⟩
    match (m.val - 2) % 8 with
    | 0 => .l false k
    | 1 => .l true k
    | 2 => .r false k
    | 3 => .r true k
    | 4 => .u false k
    | 5 => .u true k
    | 6 => .v false k
    | _ => .v true k

lemma gvInv_gvIdx {d : ℕ} (x : GV d) : gvInv (gvIdx x) = x := by
  rcases x with _ | _ | ⟨b, j⟩ | ⟨b, j⟩ | ⟨b, i⟩ | ⟨b, i⟩
  · rfl
  · rfl
  · cases b
    · have hlt : ¬ (2 + 8 * j.val < 2) := by omega
      have hm : (2 + 8 * j.val - 2) % 8 = 0 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.l false); ext; dsimp only; omega
    · have hlt : ¬ (3 + 8 * j.val < 2) := by omega
      have hm : (3 + 8 * j.val - 2) % 8 = 1 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.l true); ext; dsimp only; omega
  · cases b
    · have hlt : ¬ (4 + 8 * j.val < 2) := by omega
      have hm : (4 + 8 * j.val - 2) % 8 = 2 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.r false); ext; dsimp only; omega
    · have hlt : ¬ (5 + 8 * j.val < 2) := by omega
      have hm : (5 + 8 * j.val - 2) % 8 = 3 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.r true); ext; dsimp only; omega
  · cases b
    · have hlt : ¬ (6 + 8 * i.val < 2) := by omega
      have hm : (6 + 8 * i.val - 2) % 8 = 4 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.u false); ext; dsimp only; omega
    · have hlt : ¬ (7 + 8 * i.val < 2) := by omega
      have hm : (7 + 8 * i.val - 2) % 8 = 5 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.u true); ext; dsimp only; omega
  · cases b
    · have hlt : ¬ (8 + 8 * i.val < 2) := by omega
      have hm : (8 + 8 * i.val - 2) % 8 = 6 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.v false); ext; dsimp only; omega
    · have hlt : ¬ (9 + 8 * i.val < 2) := by omega
      have hm : (9 + 8 * i.val - 2) % 8 = 7 := by omega
      unfold gvIdx gvInv
      dsimp only
      rw [dif_neg hlt]
      generalize_proofs hp
      rw [hm]
      apply congrArg (GV.v true); ext; dsimp only; omega

lemma gvIdx_injective {d : ℕ} : Function.Injective (gvIdx (d := d)) :=
  Function.LeftInverse.injective gvInv_gvIdx

def mkEmbedding {n d : ℕ} (hdn : 2 + 8 * d ≤ n) (s t : Fin n) (_hst : s ≠ t) : GV d ↪ Fin n :=
  let a₀ : Fin n := ⟨0, by omega⟩
  let a₁ : Fin n := ⟨1, by omega⟩
  let τ₁ : Equiv.Perm (Fin n) := Equiv.swap a₀ s
  let τ₂ : Equiv.Perm (Fin n) := Equiv.swap (τ₁ a₁) t
  { toFun := fun x => τ₂ (τ₁ (Fin.castLE hdn (gvIdx x)))
    inj' := fun _ _ h => gvIdx_injective ((Fin.castLE_injective hdn) (τ₁.injective (τ₂.injective h))) }

lemma mkEmbedding_s {n d : ℕ} (hdn : 2 + 8 * d ≤ n) (s t : Fin n) (hst : s ≠ t) :
    mkEmbedding hdn s t hst GV.s = s := by
  dsimp only [mkEmbedding, gvIdx]
  let a₀ : Fin n := ⟨0, by omega⟩
  let a₁ : Fin n := ⟨1, by omega⟩
  have ha01 : a₀ ≠ a₁ := by simp [a₀, a₁, Fin.ext_iff]
  have hs1 : s ≠ (Equiv.swap a₀ s) a₁ := by
    intro h
    have heq : (Equiv.swap a₀ s) a₀ = (Equiv.swap a₀ s) a₁ := by
      rw [Equiv.swap_apply_left]
      exact h
    exact ha01 ((Equiv.swap a₀ s).injective heq)
  change (Equiv.swap ((Equiv.swap a₀ s) a₁) t) ((Equiv.swap a₀ s) a₀) = s
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hs1 hst]

lemma mkEmbedding_t {n d : ℕ} (hdn : 2 + 8 * d ≤ n) (s t : Fin n) (hst : s ≠ t) :
    mkEmbedding hdn s t hst GV.t = t := by
  dsimp only [mkEmbedding, gvIdx]
  let a₀ : Fin n := ⟨0, by omega⟩
  let a₁ : Fin n := ⟨1, by omega⟩
  change (Equiv.swap ((Equiv.swap a₀ s) a₁) t) ((Equiv.swap a₀ s) a₁) = t
  exact Equiv.swap_apply_left _ _

lemma ofReal_div_nat (a b : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((a : ℝ) / (b : ℝ)) = (a : ENNReal) / (b : ENNReal) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

lemma ennreal_one_third_add_one_fourth_lt :
    (1 / 3 : ENNReal) + (1 / 4 : ENNReal) < (2 / 3 : ENNReal) := by
  have h1 : (1 / 3 : ENNReal) = ENNReal.ofReal (1 / 3 : ℝ) := by
    simpa using (ofReal_div_nat 1 3 (by norm_num)).symm
  have h2 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by
    simpa using (ofReal_div_nat 1 4 (by norm_num)).symm
  have h3 : (2 / 3 : ENNReal) = ENNReal.ofReal (2 / 3 : ℝ) := by
    simpa using (ofReal_div_nat 2 3 (by norm_num)).symm
  rw [h1, h2, h3, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact ENNReal.ofReal_lt_ofReal_iff (by norm_num) |>.mpr (by norm_num)

lemma matrix_clause {cL η₃₃ cB : ℝ} (hcL : 0 < cL) (hη₃₃ : 0 < η₃₃) (hcB : 0 < cB)
    (h36 : Cor36Holds cL η₃₃ cB)
    {n B : ℕ} {T : ℝ}
    (hB1 : 1 ≤ B)
    (hBn : (B : ℝ) ≤ min (1 / 12000) (η₃₃ / 100) * n)
    (s t : Fin n) (hst : s ≠ t)
    (S : Type) [Fintype S] (hS : Fintype.card S ≤ 2 ^ B)
    (A : RandAlg n (Fin n × Fin n) Bool S) (hMeas : MeasurableRuns A matrixOracle)
    (hBT : (B : ℝ) * T ≤ (cB * cL / (40000 * (40 + 4096 * cB))) * (n : ℝ) ^ 2)
    (hExp : ExpAmortized A matrixOracle T) :
    ∃ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ ∧ ForestThroughout σ ∧
      (1 / 2 : ℝ) * n ≤ σ.length ∧ (σ.length : ℝ) ≤ (40 + 4096 * cB) * n ∧
      A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ} < 2 / 3 := by
  have hBn1 : (B : ℝ) ≤ (1 / 12000 : ℝ) * n :=
    hBn.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg n))
  have hBn2 : (B : ℝ) ≤ (η₃₃ / 100) * n :=
    hBn.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg n))
  have h12000 : 12000 * B ≤ n := by
    have : (12000 * B : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  let d : ℕ := (n - 2) / 8
  let B' : ℕ := max B 10
  have hdn : 2 + 8 * d ≤ n := by omega
  have hd_lo_nat : n ≤ 10 * d := by omega
  have hd_lo : (n : ℝ) / 10 ≤ (d : ℝ) := by
    have : (n : ℝ) ≤ 10 * (d : ℝ) := by exact_mod_cast hd_lo_nat
    linarith
  have hd_pos : 1 ≤ d := by omega
  have hB'10 : 10 ≤ B' := Nat.le_max_right B 10
  have hBB' : B ≤ B' := Nat.le_max_left B 10
  have hB'le10B : B' ≤ 10 * B := by omega
  have hB'd : 128 * B' ≤ d := by omega
  have hB'η : (B' : ℝ) ≤ η₃₃ * (d : ℝ) := by
    have h1 : (B' : ℝ) ≤ 10 * (B : ℝ) := by exact_mod_cast hB'le10B
    calc (B' : ℝ) ≤ 10 * (B : ℝ) := h1
      _ ≤ 10 * ((η₃₃ / 100) * n) := by linarith
      _ = η₃₃ * ((n : ℝ) / 10) := by ring
      _ ≤ η₃₃ * (d : ℝ) := mul_le_mul_of_nonneg_left hd_lo hη₃₃.le
  have hS' : Fintype.card S ≤ 2 ^ B' :=
    hS.trans (Nat.pow_le_pow_right (by norm_num) hBB')
  let e : GV d ↪ Fin n := mkEmbedding hdn s t hst
  have hes : e GV.s = s := mkEmbedding_s hdn s t hst
  have het : e GV.t = t := mkEmbedding_t hdn s t hst
  obtain ⟨red, hred⟩ := DynOracleConn.reduction (S := S) e
  let Apphp : RandPPHPAlg d S :=
    { Ω := A.Ω
      measΩ := A.measΩ
      μ := A.μ
      isProb := A.isProb
      alg := fun ω => red (A.alg ω) }
  have hMeasP : PPHPMeasurableRuns Apphp := by
    intro X ℐ P
    obtain ⟨_, _, _, F, hF⟩ := hred X ℐ
    have hEq : (fun ω => (Apphp.alg ω).transcript X ℐ) ⁻¹' P =
        (fun ω => (A.alg ω).transcript matrixOracle (hardSeq e X ℐ)) ⁻¹' (F ⁻¹' P) := by
      ext ω
      simp [Apphp, (hF (A.alg ω)).1]
    rw [hEq]
    exact hMeas (hardSeq e X ℐ) (F ⁻¹' P)
  obtain ⟨X, ℐ, h37⟩ :=
    DynOracleConn.theorem_3_7 cL η₃₃ cB h36 hB'10 hB'd hB'η hS' Apphp hMeasP
  let σ : List (PunctSketch.Update n) := hardSeq e X (List.ofFn ℐ)
  obtain ⟨hValid, hForest, hLen, F, hF⟩ := hred X (List.ofFn ℐ)
  have hℐlen : (List.ofFn ℐ).length = numEpochs cB d B' := List.length_ofFn
  have hLen' : σ.length = 8 * d - 1 + 2 * numEpochs cB d B' := by
    simpa [σ, hℐlen] using hLen
  have hκ1 : (1 / 2 : ℝ) * (n : ℝ) ≤ (σ.length : ℝ) := by
    have hnat : n ≤ 2 * σ.length := by omega
    have hreal : (n : ℝ) ≤ 2 * (σ.length : ℝ) := by exact_mod_cast hnat
    linarith
  have hB'pos : (0 : ℝ) < (B' : ℝ) := by positivity
  have hdposR : (0 : ℝ) < (d : ℝ) := by positivity
  have hceil : (⌈cB * (d : ℝ) / (B' : ℝ)⌉₊ : ℝ) ≤ cB * (d : ℝ) / (B' : ℝ) + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hEpochs_le : (numEpochs cB d B' : ℝ) ≤ (2048 * cB + 16) * (d : ℝ) := by
    have hdef : (numEpochs cB d B' : ℝ) =
        2048 * (B' : ℝ) * (⌈cB * (d : ℝ) / (B' : ℝ)⌉₊ : ℝ) := by
      unfold numEpochs; push_cast; ring
    have hB'dR : 128 * (B' : ℝ) ≤ (d : ℝ) := by exact_mod_cast hB'd
    calc (numEpochs cB d B' : ℝ)
        = 2048 * (B' : ℝ) * (⌈cB * (d : ℝ) / (B' : ℝ)⌉₊ : ℝ) := hdef
      _ ≤ 2048 * (B' : ℝ) * (cB * (d : ℝ) / (B' : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = 2048 * cB * (d : ℝ) + 2048 * (B' : ℝ) := by
          have hne : (B' : ℝ) ≠ 0 := hB'pos.ne'
          field_simp [hne]
      _ ≤ 2048 * cB * (d : ℝ) + 16 * (d : ℝ) := by linarith
      _ = (2048 * cB + 16) * (d : ℝ) := by ring
  let κ₂ : ℝ := 40 + 4096 * cB
  have hκ₂_pos : 0 < κ₂ := by positivity
  have hκ2 : (σ.length : ℝ) ≤ κ₂ * (n : ℝ) := by
    have hsub : ((8 * d - 1 : ℕ) : ℝ) ≤ 8 * (d : ℝ) := by
      have : 8 * d - 1 ≤ 8 * d := Nat.sub_le _ _
      exact_mod_cast this
    have hdnR : (d : ℝ) ≤ (n : ℝ) := by
      have : 8 * d ≤ n := by omega
      have : 8 * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    calc (σ.length : ℝ)
        = ((8 * d - 1 : ℕ) : ℝ) + 2 * (numEpochs cB d B' : ℝ) := by
            rw [hLen']; push_cast; ring
      _ ≤ 8 * (d : ℝ) + 2 * ((2048 * cB + 16) * (d : ℝ)) := by linarith
      _ = κ₂ * (d : ℝ) := by ring
      _ ≤ κ₂ * (n : ℝ) := mul_le_mul_of_nonneg_left hdnR hκ₂_pos.le
  let M : ℝ := cB * cL * (d : ℝ) ^ 3 / (B' : ℝ)
  have hM_pos : 0 < M := by positivity
  have hBudget : (σ.length : ℝ) * T ≤ M / 4 := by
    by_cases hT : T ≤ 0
    · have : (σ.length : ℝ) * T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hT
      linarith
    · push Not at hT
      have hB'le10BR : (B' : ℝ) ≤ 10 * (B : ℝ) := by exact_mod_cast hB'le10B
      have hB'T : (B' : ℝ) * T ≤ 10 * ((B : ℝ) * T) := by nlinarith
      let c : ℝ := cB * cL / (40000 * κ₂)
      have hB'T2 : (B' : ℝ) * T ≤ 10 * c * (n : ℝ) ^ 2 := by
        have : (B : ℝ) * T ≤ c * (n : ℝ) ^ 2 := hBT
        linarith
      have hT_bound : T ≤ 10 * c * (n : ℝ) ^ 2 / (B' : ℝ) := by
        rw [le_div_iff₀ hB'pos]
        linarith
      have hn3 : (n : ℝ) ^ 3 ≤ 1000 * (d : ℝ) ^ 3 := by
        have hn10 : (n : ℝ) ≤ 10 * (d : ℝ) := by linarith
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [sq_nonneg (n : ℝ), sq_nonneg (10 * (d : ℝ) - (n : ℝ))]
      calc (σ.length : ℝ) * T
          ≤ (κ₂ * (n : ℝ)) * (10 * c * (n : ℝ) ^ 2 / (B' : ℝ)) :=
            mul_le_mul hκ2 hT_bound hT.le (by positivity)
        _ = 10 * κ₂ * c * (n : ℝ) ^ 3 / (B' : ℝ) := by ring
        _ ≤ 10 * κ₂ * c * (1000 * (d : ℝ) ^ 3) / (B' : ℝ) := by
            apply div_le_div_of_nonneg_right _ hB'pos.le
            exact mul_le_mul_of_nonneg_left hn3 (by positivity)
        _ = M / 4 := by
            dsimp [M, c]
            have hκne : κ₂ ≠ 0 := hκ₂_pos.ne'
            have hBne : (B' : ℝ) ≠ 0 := hB'pos.ne'
            field_simp [hκne, hBne]
            ring
  let f : A.Ω → ENNReal := fun ω => ((A.alg ω).totalCost matrixOracle σ : ENNReal)
  have hf_meas : Measurable f := by
    let g : List (List ((Fin n × Fin n) × Bool) × Bool) → ENNReal :=
      fun tr => Nat.cast ((tr.map (fun p => p.1.length)).sum)
    intro U _
    have hpre : f ⁻¹' U = (fun ω => (A.alg ω).transcript matrixOracle σ) ⁻¹' (g ⁻¹' U) := by
      ext ω; simp [f, g, DetAlg.totalCost]
    rw [hpre]
    exact hMeas σ (g ⁻¹' U)
  have hInt : ∫⁻ ω, f ω ∂A.μ ≤ ENNReal.ofReal (M / 4) :=
    (hExp σ hValid hForest).trans (ENNReal.ofReal_le_ofReal hBudget)
  let BadCost : Set A.Ω := {ω | M < ((A.alg ω).totalCost matrixOracle σ : ℝ)}
  have hBadSub : BadCost ⊆ {ω | ENNReal.ofReal M ≤ f ω} := by
    intro ω hω
    dsimp [BadCost] at hω
    dsimp [f]
    have : ENNReal.ofReal M ≤ ENNReal.ofReal (((A.alg ω).totalCost matrixOracle σ : ℕ) : ℝ) :=
      ENNReal.ofReal_le_ofReal hω.le
    simpa using this
  have hMarkov1 : ENNReal.ofReal M * A.μ BadCost ≤ ENNReal.ofReal (M / 4) := by
    have hmono : A.μ BadCost ≤ A.μ {ω | ENNReal.ofReal M ≤ f ω} := measure_mono hBadSub
    calc ENNReal.ofReal M * A.μ BadCost
        ≤ ENNReal.ofReal M * A.μ {ω | ENNReal.ofReal M ≤ f ω} := by gcongr
      _ ≤ ∫⁻ ω, f ω ∂A.μ := mul_meas_ge_le_lintegral₀ hf_meas.aemeasurable (ENNReal.ofReal M)
      _ ≤ ENNReal.ofReal (M / 4) := hInt
  have hBadBound : A.μ BadCost ≤ (1 / 4 : ENNReal) := by
    have hR : ENNReal.ofReal (M / 4) = ENNReal.ofReal M * (1 / 4 : ENNReal) := by
      have hdiv : M / 4 = M * (1 / 4 : ℝ) := by ring
      have h14 : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ENNReal) := by
        simpa using ofReal_div_nat 1 4 (by norm_num)
      rw [hdiv, ENNReal.ofReal_mul hM_pos.le, h14]
    rw [hR] at hMarkov1
    have hne0 : ENNReal.ofReal M ≠ 0 := by simp [hM_pos]
    have hneTop : ENNReal.ofReal M ≠ ⊤ := ENNReal.ofReal_ne_top
    calc A.μ BadCost
        = 1 * A.μ BadCost := (one_mul _).symm
      _ = ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal M) * A.μ BadCost := by
          rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (ENNReal.ofReal M)⁻¹ * (ENNReal.ofReal M * A.μ BadCost) := mul_assoc _ _ _
      _ ≤ (ENNReal.ofReal M)⁻¹ * (ENNReal.ofReal M * (1 / 4 : ENNReal)) := by gcongr
      _ = ((ENNReal.ofReal M)⁻¹ * ENNReal.ofReal M) * (1 / 4 : ENNReal) := (mul_assoc _ _ _).symm
      _ = 1 * (1 / 4 : ENNReal) := by rw [ENNReal.inv_mul_cancel hne0 hneTop]
      _ = (1 / 4 : ENNReal) := one_mul _
  let Good37 : Set A.Ω :=
    {ω | (red (A.alg ω)).correctTotal X (List.ofFn ℐ) ∧
      ((red (A.alg ω)).Ltotal X (List.ofFn ℐ) : ℝ) ≤ M}
  have h37' : A.μ Good37 ≤ (1 / 3 : ENNReal) := h37
  have hSubAll : {ω | (A.alg ω).AllCorrect matrixOracle s t σ} ⊆ Good37 ∪ BadCost := by
    intro ω hω
    by_cases hC : M < ((A.alg ω).totalCost matrixOracle σ : ℝ)
    · exact Or.inr hC
    · push Not at hC
      left
      have hω' : (A.alg ω).AllCorrect matrixOracle (e GV.s) (e GV.t) σ := by
        simpa [hes, het] using hω
      refine ⟨(hF (A.alg ω)).2.1 hω', ?_⟩
      have hLle : ((red (A.alg ω)).Ltotal X (List.ofFn ℐ) : ℝ) ≤
          ((A.alg ω).totalCost matrixOracle σ : ℝ) := by
        exact_mod_cast (hF (A.alg ω)).2.2
      exact hLle.trans hC
  have hProb : A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ} < (2 / 3 : ENNReal) := by
    calc A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ}
        ≤ A.μ (Good37 ∪ BadCost) := measure_mono hSubAll
      _ ≤ A.μ Good37 + A.μ BadCost := measure_union_le _ _
      _ ≤ (1 / 3 : ENNReal) + (1 / 4 : ENNReal) := add_le_add h37' hBadBound
      _ < (2 / 3 : ENNReal) := ennreal_one_third_add_one_fourth_lt
  exact ⟨σ, hValid, hForest, hκ1, hκ2, hProb⟩

end AuxThm4

theorem solution :
    ∃ η c κ₁ κ₂ : ℝ, 0 < η ∧ 0 < c ∧ 0 < κ₁ ∧ 0 < κ₂ ∧
      ∀ (n B : ℕ) (T : ℝ), 1 ≤ B → (B : ℝ) ≤ η * n →
      ∀ s t : Fin n, s ≠ t →
      ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B →
        (∀ A : RandAlg n (Fin n × Fin n) Bool S, MeasurableRuns A matrixOracle →
          (B : ℝ) * T ≤ c * (n : ℝ) ^ 2 → ExpAmortized A matrixOracle T →
          ∃ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ ∧ ForestThroughout σ ∧
            κ₁ * n ≤ σ.length ∧ (σ.length : ℝ) ≤ κ₂ * n ∧
            A.μ {ω | (A.alg ω).AllCorrect matrixOracle s t σ} < 2 / 3) ∧
        (∀ A : RandAlg n (ListQuery n) ℕ S, MeasurableRuns A listOracle →
          (B : ℝ) * T ≤ c * (n : ℝ) → ExpAmortized A listOracle T →
          ∃ σ : List (PunctSketch.Update n), PunctSketch.IsValidStream σ ∧ ForestThroughout σ ∧
            κ₁ * n ≤ σ.length ∧ (σ.length : ℝ) ≤ κ₂ * n ∧
            A.μ {ω | (A.alg ω).AllCorrect listOracle s t σ} < 2 / 3) := by
  obtain ⟨cL, η₃₃, hcL, hη₃₃, h33⟩ := DynOracleConn.corollary_3_3
  obtain ⟨cB, hcB, h36⟩ := DynOracleConn.corollary_3_6 cL η₃₃ hcL h33
  let η : ℝ := min (1 / 12000) (η₃₃ / 100)
  let κ₁ : ℝ := 1 / 2
  let κ₂ : ℝ := 40 + 4096 * cB
  let c : ℝ := cB * cL / (40000 * κ₂)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hκ₁ : 0 < κ₁ := by norm_num
  have hκ₂ : 0 < κ₂ := by positivity
  have hc : 0 < c := by positivity
  refine ⟨η, c, κ₁, κ₂, hη, hc, hκ₁, hκ₂, ?_⟩
  intro n B T hB1 hBn s t hst S _ hS
  refine ⟨?_, ?_⟩
  · intro A hMeas hBT hExp
    exact AuxThm4.matrix_clause hcL hη₃₃ hcB h36 hB1 hBn s t hst S hS A hMeas hBT hExp
  · intro A hMeas hBT hExp
    obtain ⟨sim, hsim⟩ := DynOracleConn.list_to_matrix (n := n) (S := S)
    let Amat : RandAlg n (Fin n × Fin n) Bool S :=
      { Ω := A.Ω
        measΩ := A.measΩ
        μ := A.μ
        isProb := A.isProb
        alg := fun ω => sim (A.alg ω) }
    have hMeasM : MeasurableRuns Amat matrixOracle := by
      intro σ P
      obtain ⟨F, hF⟩ := hsim σ
      have hEq : (fun ω => (Amat.alg ω).transcript matrixOracle σ) ⁻¹' P =
          (fun ω => (A.alg ω).transcript listOracle σ) ⁻¹' (F ⁻¹' P) := by
        ext ω
        simp [Amat, (hF (A.alg ω)).1]
      rw [hEq]
      exact hMeas σ (F ⁻¹' P)
    have hBTM : (B : ℝ) * ((n : ℝ) * T) ≤ c * (n : ℝ) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      calc (B : ℝ) * ((n : ℝ) * T)
          = (n : ℝ) * ((B : ℝ) * T) := by ring
        _ ≤ (n : ℝ) * (c * (n : ℝ)) := mul_le_mul_of_nonneg_left hBT hn0
        _ = c * (n : ℝ) ^ 2 := by ring
    have hExpM : ExpAmortized Amat matrixOracle ((n : ℝ) * T) := by
      intro σ hV hFor
      obtain ⟨_, hF⟩ := hsim σ
      have hle : ∀ ω, ((Amat.alg ω).totalCost matrixOracle σ : ENNReal) ≤
          (n : ENNReal) * ((A.alg ω).totalCost listOracle σ : ENNReal) := by
        intro ω
        have hnat := (hF (A.alg ω)).2.2
        exact_mod_cast hnat
      have hMeasCost : Measurable (fun ω => ((A.alg ω).totalCost listOracle σ : ENNReal)) := by
        let g : List (List (ListQuery n × ℕ) × Bool) → ENNReal :=
          fun tr => Nat.cast ((tr.map (fun p => p.1.length)).sum)
        intro U _
        have hpre : (fun ω => ((A.alg ω).totalCost listOracle σ : ENNReal)) ⁻¹' U =
            (fun ω => (A.alg ω).transcript listOracle σ) ⁻¹' (g ⁻¹' U) := by
          ext ω; simp [g, DetAlg.totalCost]
        rw [hpre]
        exact hMeas σ (g ⁻¹' U)
      calc ∫⁻ ω, ((Amat.alg ω).totalCost matrixOracle σ : ENNReal) ∂Amat.μ
          ≤ ∫⁻ ω, (n : ENNReal) * ((A.alg ω).totalCost listOracle σ : ENNReal) ∂A.μ :=
            lintegral_mono hle
        _ = (n : ENNReal) * ∫⁻ ω, ((A.alg ω).totalCost listOracle σ : ENNReal) ∂A.μ :=
            lintegral_const_mul (n : ENNReal) hMeasCost
        _ ≤ (n : ENNReal) * ENNReal.ofReal ((σ.length : ℝ) * T) := by
            have hE := hExp σ hV hFor
            gcongr
        _ ≤ ENNReal.ofReal ((σ.length : ℝ) * ((n : ℝ) * T)) := by
            by_cases hpos : 0 ≤ (σ.length : ℝ) * T
            · have hn_eq : (n : ENNReal) = ENNReal.ofReal (n : ℝ) :=
                (ENNReal.ofReal_natCast n).symm
              rw [hn_eq, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
              exact ENNReal.ofReal_le_ofReal (by ring_nf; rfl)
            · push Not at hpos
              rw [ENNReal.ofReal_of_nonpos hpos.le, mul_zero]
              exact zero_le
    obtain ⟨σ, hV, hFor, h1, h2, hProb⟩ :=
      AuxThm4.matrix_clause hcL hη₃₃ hcB h36 hB1 hBn s t hst S hS Amat hMeasM hBTM hExpM
    refine ⟨σ, hV, hFor, h1, h2, ?_⟩
    obtain ⟨_, hF⟩ := hsim σ
    have hSetEq : {ω | (A.alg ω).AllCorrect listOracle s t σ} =
        {ω | (Amat.alg ω).AllCorrect matrixOracle s t σ} := by
      ext ω
      simp only [Set.mem_ofPred_eq, DetAlg.AllCorrect, Amat, (hF (A.alg ω)).2.1]
    rw [hSetEq]
    exact hProb
