-- Prove2me | solution 1 for DetDLP.m89_s1_count_oracle
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:38:18.97168+00:00
-- url     : https://prove2.me/submissions/7ae54990-3c43-4ba9-9b18-dc952448a312

import Theorems.Thm_DetDLP_m89_s1_query_graph_words
import Theorems.Thm_DetDLP_m89_s1_word_pipe
import Theorems.Thm_DetDLP_m89_s1_count_output_decode
import Definitions.Def_DetDLP_PolyTBridge
import Definitions.Def_DetDLP_M89_MachineComp
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem DetDLP.m89_s1_poly_input_absorb (L K : ℕ) : ∃ Q, ∀ n b : ℕ, n ≤ L*(b+1)^L → polyBound K n ≤ polyBound Q b := by
  let Q := max (K*(L+1)^K) (L*K)
  refine ⟨Q,?_⟩
  intro n b hn
  have hp : (1:ℝ) ≤ (b:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
  have hbl : (1:ℝ) ≤ ((b:ℝ)+1)^L := one_le_pow₀ hp
  have hn' : (n:ℝ) ≤ (L:ℝ)*((b:ℝ)+1)^L := by exact_mod_cast hn
  have hsum : (n:ℝ)+1 ≤ ((L:ℝ)+1)*((b:ℝ)+1)^L := by nlinarith
  unfold polyBound
  calc _ ≤ (K:ℝ)*(((L:ℝ)+1)*((b:ℝ)+1)^L)^K := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) (by positivity)
       _ = ((K:ℝ)*((L:ℝ)+1)^K)*((b:ℝ)+1)^(L*K) := by rw [mul_pow,pow_mul]; ring
       _ ≤ _ := mul_le_mul (by exact_mod_cast (le_max_left (K*(L+1)^K) (L*K))) (pow_le_pow_right₀ hp (le_max_right ..)) (by positivity) (by positivity)

private theorem DetDLP.m89_s1_poly_as_power (Q u : ℕ) (hu : 2 ≤ u) : polyBound Q u ≤ (u:ℝ)^(2*Q+Q+1) := by
  have hu' : (2:ℝ) ≤ u := by exact_mod_cast hu
  have hbase : (1:ℝ) ≤ u := by linarith
  have hQ : (Q:ℝ) ≤ (u:ℝ)^Q := by exact_mod_cast (Nat.lt_two_pow_self (n := Q)).le.trans (Nat.pow_le_pow_left hu Q)
  have hsum : (u:ℝ)+1 ≤ (u:ℝ)^2 := by nlinarith
  calc polyBound Q u ≤ (u:ℝ)^Q*((u:ℝ)^2)^Q := mul_le_mul hQ (pow_le_pow_left₀ (by positivity) hsum Q) (by positivity) (by positivity)
       _ = (u:ℝ)^(Q+2*Q) := by rw [pow_add,pow_mul]
       _ ≤ _ := pow_le_pow_right₀ hbase (by omega)

theorem solution :
    ((∀ (G : BipartiteMultigraph)
        (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
        {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
        (P0 : ℕ),
        IsParsimonious G T ext R →
        G.nE < P0 →
        (Finset.univ.filter R).card < 2 ^ P0 ∧
        BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
          truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) ∧
     (∀ (enet Δnet : ℕ),
        let sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
        2 ≤ sBTN ∧ enet < sBTN ∧ Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10))) ∧
     (∀ (p n T m gord H₀ H₁ A₀ B₀ J₀ A₁ B₁ J₁ : ℕ),
        0 < p → 0 < n → 0 < T → 0 < H₀ → 0 < H₁ →
        let μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
        (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ) + 64 * μ ^ 2 * (H₀ : ℝ)) /
            (μ ^ 2 * (H₀ : ℝ)) ≤
          ((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ) + 64 * μ ^ 2 * (H₁ : ℝ)) /
            (μ ^ 2 * (H₁ : ℝ))) ↔
        (((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
            64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
            128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) ≤
          ((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
            64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
            128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ))) ∧
     (∀ (b r v p : ℕ), r ≤ b → p ≤ 2 ^ b →
        ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ u < p)).card =
          min ((v + 1) * 2 ^ (b - r)) p - min (v * 2 ^ (b - r)) p ∧
        ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ 1 ≤ u ∧ u < p)).card =
          min ((v + 1) * 2 ^ (b - r)) p - min (max (v * 2 ^ (b - r)) 1) p)) →
    ((∀ (q x y z : ℕ) (γ : Bool) (ssum : ℕ),
        x < q → y < q → z < q →
        ((x + y = ssum ∧ z + (if γ then 1 else 0) * q = ssum) ↔
          (z = (x + y) % q ∧ γ = decide (q ≤ x + y) ∧ ssum = x + y))) ∧
     (∀ (q x y z θ u₁ u₂ : ℕ),
        x < q → y < q → z < q →
        ((x * y = u₁ ∧ θ * q = u₂ ∧ u₂ + z = u₁) ↔
          (z = (x * y) % q ∧ θ = (x * y) / q ∧ θ < q ∧ u₁ = x * y ∧ u₂ = ((x * y) / q) * q))) ∧
     (∀ (p : ℕ) [Fact p.Prime] (u : ZMod p) (ζ : Bool) (winv : ZMod p),
        (((if ζ then (1 : ZMod p) else 0) * u = 0 ∧
          (if ζ then (1 : ZMod p) else 0) * winv = 0 ∧
          (1 - (if ζ then (1 : ZMod p) else 0)) * (u * winv) =
            1 - (if ζ then (1 : ZMod p) else 0)) ↔
         (ζ = decide (u = 0) ∧ winv = u⁻¹))) ∧
     ((∀ (ι₁ ι₂ ζx ζy : Bool),
         let b : Bool → ℤ := fun x => if x then 1 else 0
         let σ₁ := b ι₁
         let σ₂ := (1 - b ι₁) * b ι₂
         let σ₃ := (1 - b ι₁) * (1 - b ι₂) * b ζx * b ζy
         let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
         let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
         (σ₁ = 0 ∨ σ₁ = 1) ∧ (σ₂ = 0 ∨ σ₂ = 1) ∧ (σ₃ = 0 ∨ σ₃ = 1) ∧
         (σ₄ = 0 ∨ σ₄ = 1) ∧ (σ₅ = 0 ∨ σ₅ = 1) ∧
         σ₁ + σ₂ + σ₃ + σ₄ + σ₅ = 1) ∧
      (∀ (p : ℕ) [Fact p.Prime], 2 < p →
         ∀ (aE bE x₁ y₁ x₂ y₂ lsl : ZMod p) (ι₁ ι₂ : Bool),
           y₁ ^ 2 = x₁ ^ 3 + aE * x₁ + bE →
           y₂ ^ 2 = x₂ ^ 3 + aE * x₂ + bE →
           let ζx := decide (x₂ - x₁ = 0)
           let ζy := decide (y₁ + y₂ = 0)
           let b : Bool → ZMod p := fun x => if x then 1 else 0
           let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
           let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
           ((σ₄ * ((x₂ - x₁) * lsl - (y₂ - y₁)) = 0 ∧
             σ₅ * (2 * y₁ * lsl - (3 * x₁ ^ 2 + aE)) = 0 ∧
             (1 - σ₄ - σ₅) * lsl = 0) ↔
            lsl =
              if (!ι₁ && !ι₂ && !ζx) then (y₂ - y₁) * (x₂ - x₁)⁻¹
              else if (!ι₁ && !ι₂ && ζx && !ζy) then (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹
              else 0)))) →
    (∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s → G.nE ≤ C * s → G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s → 1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))) →
    CountOracle := by
  classical
  intro hc hg contract
  obtain ⟨make,port,L,hm,ht,graph⟩ := m89_s1_query_graph_words hg
  obtain ⟨P,op,I,prep⟩ := PolyTBridge.polyT_listBool_runsWithin make hm
  obtain ⟨E,oe,J,eval⟩ := PolyTBridge.polyT_listBool_runsWithin port ht
  obtain ⟨Q,hQ⟩ := DetDLP.m89_s1_poly_input_absorb L J
  let d := max (L+1) (2*Q+Q+1)
  have hd : 0 < d := Nat.lt_of_lt_of_le (Nat.zero_lt_succ L) (le_max_left ..)
  obtain ⟨A,oa,K,run⟩ := contract 1 1 d (by decide) (by decide) hd E oe
  obtain ⟨U,hU⟩ := DetDLP.m89_s1_poly_input_absorb L I
  obtain ⟨V,hV⟩ := DetDLP.m89_s1_poly_input_absorb L K
  obtain ⟨W,hW⟩ := stage1_complexity_dominance.2.2.2 K L L
  obtain ⟨Z,hZ⟩ := stage1_complexity_dominance.2.2.1 U 0
  let mono := stage1_complexity_dominance.1
  obtain ⟨M,o,C,pipe⟩ := m89_s1_word_pipe P op A oa (max U Z) (max W V) true
  refine ⟨M,o,C,?_⟩
  intro w b n h
  have hp : ∃ p, 2 ≤ p ∧ bitLen p = b := by
    cases h <;> exact ⟨_,(Fact.out : Nat.Prime _).two_le,rfl⟩
  obtain ⟨p,hp,rfl⟩ := hp
  let b := bitLen p
  have h1 : 1 ≤ bitLen p := by
    by_contra! hl
    have h0 : bitLen p = 0 := by omega
    have hp2 : p ≤ 2^(bitLen p) := Nat.le_pow_clog (by decide) p
    rw [h0] at hp2
    omega
  obtain ⟨s,G,T,k,ext,R,hpar,hn,hs,hb,he,hv,hdeg,hlin,hpoly,hmake,hport⟩ := graph w b n h
  let u := s+w.length
  let F := fun (v : Fin G.nV) (a : Fin (G.deg v) → Bool) => truncPolyOfCoeffs s 1 (fun _ => if T v a then 1 else 0)
  have hpow : 1 < 2^s := Nat.one_lt_pow (by omega) (by decide)
  have hentry : BTNEntryEvaluable w G s 1 F E oe
      ((u:ℝ)^d*(2:ℝ)^((1:ℝ)*(s:ℝ)^((9:ℝ)/10))) ((u:ℝ)^d) := by
    intro v a
    let z := encodePortQuery w v.val (List.ofFn a)
    obtain ⟨hlen, hy⟩ := hport v a
    let bit : ℕ := if T v a then 1 else 0
    refine ⟨port z, ?_, ?_⟩
    · refine ⟨fun _ => bit,fun _ => ?_,?_,rfl⟩
      · dsimp [bit]; split <;> omega
      · rw [hy]; simp [bit]
    · have hu2 : 2 ≤ u := by dsimp [u]; omega
      have ht0 := hQ z.length u hlen
      have ht1 := DetDLP.m89_s1_poly_as_power Q u hu2
      have hbase : (1:ℝ) ≤ (u:ℝ) := by exact_mod_cast (show 1 ≤ u by omega)
      have hallow := (ht0.trans ht1).trans (pow_le_pow_right₀ hbase (le_max_right (L+1) (2*Q+Q+1)))
      apply MachineComposition.runsWithin_mono (eval z) _ hallow
      exact hallow.trans (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by norm_num) (by positivity)))
  have hnv : G.nV ≤ s^d := hv.trans (Nat.pow_le_pow_right (by omega) ((Nat.le_succ L).trans (le_max_left ..)))
  obtain ⟨y,hy,hr⟩ := run s s 1 w G F hs (by simpa using he.le) hnv hdeg (by omega) (by simp) (by decide) (by simp; omega) (by simpa only [Nat.cast_one] using hentry)
  obtain ⟨hnlt,heq⟩ := hc.1 G T ext (fun x => R x = true) s hpar he
  rw [hn] at heq hnlt
  change EncodesTruncPoly s 1 y (BTNContract G _) at hy
  rw [heq] at hy
  have hy' := m89_s1_count_output_decode s n hnlt hy
  subst y
  have prep0 := prep w
  rw [hmake] at prep0
  have hpLen := hU w.length b ((Nat.le_add_left w.length s).trans hpoly)
  have hz := (hZ p 0 hp (by omega)).1
  have hprep := MachineComposition.runsWithin_mono prep0 ((hpLen.trans hz).trans (mono _ _ _ (le_max_right U Z)).1) (hpLen.trans (mono _ _ _ (le_max_left U Z)).2)
  have hrun := MachineComposition.runsWithin_mono hr ((hW p u s hp hlin hb ((Nat.le_add_right s w.length).trans hlin)).trans (mono _ _ _ (le_max_left W V)).1) ((hV u b hpoly).trans (mono _ _ _ (le_max_right W V)).2)
  exact pipe _ h1 _ _ _ hprep hrun
