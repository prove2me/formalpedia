-- Prove2me | solution 2 for DetDLP.prime_power_component_scan_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T17:55:03.979283+00:00
-- url     : https://prove2.me/submissions/72884615-199e-4d8f-a444-9283dd975990

import Theorems.Thm_DetDLP_m89_scan_kernel_machine
import Theorems.Thm_DetDLP_m89_four_call_word_composition
import Theorems.Thm_DetDLP_m89_prime_predecessor_factor_oracle
import Theorems.Thm_DetDLP_m89_flatten_factor_blocks_machine
import Theorems.Thm_DetDLP_m89_scan_arithmetic_correct
import Theorems.Thm_DetDLP_stage1_complexity_dominance
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private lemma frlen (x : List Bool) : x.length ≤ (Encoding.frame x).length := by
  induction x with
  | nil => simp
  | cons b xs ih => change xs.length+1 ≤ (Encoding.frame xs).length+1+1; omega
private lemma llen (x : List ℕ) : x.length ≤ (encodeNatListBin x).length := by
  induction x with
  | nil => simp
  | cons b xs ih => change xs.length+1 ≤ ((Encoding.frame (countWord b)) ++ encodeNatListBin xs).length+1; simp; omega
private lemma plen (a b d : List Bool) : d.length ≤ (Encoding.encodeList id [a,b,d]).length := by
  simp [Encoding.encodeList]; have := frlen d; omega

theorem solution
    (Mf : PrimitiveMachine) (ofac : Fin Mf.tapeCount) (Kf : ℕ)
    (hfac : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Mf ofac (countWord N) (encodeNatListBin N.primeFactorsList)
        ((2 : ℝ)^((Kf : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kf n))
    (Me : PrimitiveMachine) (oe : Fin Me.tapeCount) (Ke : ℕ) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∀ F : Fin m → List (ZMod p)ˣ,
          RunsWithin Me oe (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound Ke b) (mainSpaceBound Ke b) →
          let n := p-1
          let U := (List.ofFn F).flatten
          let h : (ZMod p)ˣ := ∏ r ∈ n.primeFactors,
            ((U.find? (fun u => decide (u^(n/r) ≠ 1))).getD 1) ^ (n / r^(n.factorization r))
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C b) (mainSpaceBound C b) := by
  obtain ⟨A,oA,hA⟩ := m89_prime_predecessor_factor_oracle Mf ofac _ _ hfac
  obtain ⟨D,oD,hD⟩ := m89_flatten_factor_blocks_machine
  obtain ⟨E,oE,K,hE⟩ := m89_scan_kernel_machine
  obtain ⟨monoC,fac,dom,_⟩ := stage1_complexity_dominance
  let L := 100 + 13*Mf.tapeCount + 2*K + Kf
  obtain ⟨J,hJ⟩ := dom L 0
  let k := J+Ke+Kf
  obtain ⟨M,o,c,hm⟩ := m89_four_call_word_composition A oA Me oe D oD E oE k
  refine ⟨M,o,c,?_⟩
  intro p hp
  dsimp only
  intro F he
  let U := (List.ofFn F).flatten
  let us := U.map M89Scan.unitRep
  let fs := (p-1).primeFactorsList
  let pkt := Encoding.encodeList id [countWord p,encodeNatListBin fs,encodeNatListBin us]
  let W := mainSpaceBound k (bitLen p)
  have hprime : p.Prime := Fact.out
  have h2 := hprime.two_le
  have wL : polyBound L (bitLen p) ≤ W := (hJ p 0 h2 (by omega)).1.trans (monoC J k _ (by dsimp [k]; omega)).1
  have pow1 : (1 : ℝ) ≤ ((bitLen p : ℝ)+1)^L := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) (bitLen p)] : (1:ℝ) ≤ (bitLen p : ℝ)+1)
  have lw : (L : ℝ) ≤ W := le_trans (by simpa [polyBound] using mul_le_mul_of_nonneg_left pow1 (Nat.cast_nonneg (α:=ℝ) L)) wL
  have wK : polyBound K (bitLen p) + K ≤ W := by
    have hKL : K ≤ L := by dsimp [L]; omega
    have hh := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α:=ℝ) (bitLen p)] : 1 ≤ (bitLen p : ℝ)+1) hKL
    have hK : (2:ℝ)*K ≤ L := by exact_mod_cast (by dsimp [L]; omega : 2*K ≤ L)
    unfold polyBound at wL ⊢
    nlinarith only [wL,mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) K),mul_le_mul_of_nonneg_right hK (show 0 ≤ ((bitLen p:ℝ)+1)^L by positivity),mul_le_mul_of_nonneg_left pow1 (Nat.cast_nonneg (α:=ℝ) K)]
  have Knon := Nat.cast_nonneg (α:=ℝ) K
  have pk0 : 0 ≤ polyBound K (bitLen p) := by unfold polyBound; positivity
  have w63 : (63:ℝ) ≤ W := le_trans (by exact_mod_cast (by dsimp [L]; omega : 63 ≤ L)) lw
  have boundA := hA p hprime
  have hsub : p-1+1=p := by omega
  rw [hsub] at boundA
  have hAf : RunsWithin A oA (countWord p) (encodeNatListBin fs) (W+1) (W+1) := by
    apply MachineComposition.runsWithin_mono boundA
    · split_ifs
      · linarith
      · have hv := (fac Kf (bitLen p)).trans (monoC Kf k _ (by dsimp [k]; omega)).1
        change _ ≤ W at hv; linarith
    · split_ifs
      · have hc : 13*Mf.tapeCount ≤ L := by dsimp [L]; omega
        have hh : ((13*Mf.tapeCount:ℕ):ℝ) ≤ L := by exact_mod_cast hc
        linarith
      · have hh := (monoC Kf L (bitLen p) (by dsimp [L]; omega)).2.trans wL; linarith
  have hMe := (monoC Ke k (bitLen p) (by dsimp [k]; omega)).1
  change _ ≤ W at hMe
  have hDr := hD p F
  have hEr := hE p U
  have hu : (U.length : ℝ) ≤ pkt.length := by
    exact_mod_cast (calc U.length = us.length := by simp [us]
                         _ ≤ (encodeNatListBin us).length := llen us
                         _ ≤ pkt.length := plen ..)
  have ht := hm p h2 (countWord p) (encodeNatListBin fs) (encodeFpFactorBlocks F) (encodeNatListBin us)
    (countWord (M89Scan.scan p fs us)) hAf (MachineComposition.runsWithin_mono he (by linarith) (by linarith))
  have hrun := ht (MachineComposition.runsWithin_mono hDr (by
    change _ ≤ (W+1)*_; push_cast; nlinarith [mul_nonneg (sub_nonneg.mpr w63) (Nat.cast_nonneg (α:=ℝ) (encodeFpFactorBlocks F).length)]) (by
    change _ ≤ (W+1)*_; push_cast; nlinarith [mul_nonneg (sub_nonneg.mpr w63) (Nat.cast_nonneg (α:=ℝ) (encodeFpFactorBlocks F).length)]))
    (MachineComposition.runsWithin_mono hEr (by
      change polyBound K (bitLen p) * _ ≤ (W+1)*(pkt.length+1 : ℝ)
      apply mul_le_mul <;> first | positivity | linarith) (by
      change polyBound K (bitLen p) + K*(_+1) ≤ (W+1)*(pkt.length+1 : ℝ)
      change polyBound K (bitLen p) + K*(pkt.length+1 : ℝ) ≤ _
      nlinarith only [wK,Knon,pk0,Nat.cast_nonneg (α:=ℝ) pkt.length,mul_nonneg (show 0 ≤ W-K by linarith) (Nat.cast_nonneg (α:=ℝ) pkt.length)]))
  change RunsWithin M o _ (countWord (M89Scan.scan p (p-1).primeFactorsList (U.map M89Scan.unitRep))) _ _ at hrun
  rw [m89_scan_arithmetic_correct] at hrun
  exact hrun

#print axioms solution
