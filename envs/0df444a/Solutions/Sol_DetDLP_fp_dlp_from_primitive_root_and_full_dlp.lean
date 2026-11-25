-- Prove2me | solution 1 for DetDLP.fp_dlp_from_primitive_root_and_full_dlp
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T20:30:48.278803+00:00
-- url     : https://prove2.me/submissions/81bf9ef9-71ec-4adc-8db2-9db22f7cf2c6

import Theorems.Thm_DetDLP_fp_dlp_machine_computes_bezout_residue

set_option autoImplicit false

open DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∃ (M_pr : PrimitiveMachine) (out_pr : Fin M_pr.tapeCount) (C_pr : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ h : (ZMod p)ˣ,
          orderOf h = p - 1 ∧
          RunsWithin M_pr out_pr (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C_pr (bitLen p)) (mainSpaceBound C_pr (bitLen p))) →
    (∃ (M_full : PrimitiveMachine) (out_full : Fin M_full.tapeCount) (C_full : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        orderOf h = p - 1 →
        ∃ u : ℕ, u < p - 1 ∧ h ^ u = a ∧
          RunsWithin M_full out_full (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val)
            (countWord u)
            (mainTimeBound C_full (bitLen p)) (mainSpaceBound C_full (bitLen p))) →
    (∃ (M_fp : PrimitiveMachine) (out_fp : Fin M_fp.tapeCount) (C_fp : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (g t : (ZMod p)ˣ),
        (t ∉ Subgroup.zpowers g →
          RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
            (encodeOptionNatBin none)
            (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) ∧
        (t ∈ Subgroup.zpowers g →
          ∃ x : ℕ, x < orderOf g ∧ g ^ x = t ∧
            RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
              (encodeOptionNatBin (some x))
              (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p)))) := by
  intro hpr hfull
  obtain ⟨M, out, C, hM⟩ := fp_dlp_machine_computes_bezout_residue hpr hfull
  obtain ⟨_, _, _, hroot⟩ := hpr
  obtain ⟨_, _, _, hlog⟩ := hfull
  refine ⟨M, out, C, ?_⟩
  intro p hp g t
  obtain ⟨h, hh, _⟩ := hroot p
  obtain ⟨u, hu, hgu, _⟩ := hlog p h g hh
  obtain ⟨v, hv, htv, _⟩ := hlog p h t hh
  let n := p - 1
  let d := Nat.gcd u n
  let z : ℤ := Nat.gcdA u n * ((v / d : ℕ) : ℤ)
  let x := (z % (((n/d : ℕ) : ℤ))).toNat
  have hout := hM p h g t u v hh hu hv hgu htv
  change RunsWithin M out _ (encodeOptionNatBin (if d ∣ v then some x else none)) _ _ at hout
  have horder : orderOf g = n/d := by
    rw [← hgu, orderOf_pow, hh, Nat.gcd_comm]
  have hpos : 0 < (↑(n/d) : ℤ) := by exact_mod_cast horder ▸ orderOf_pos g
  have hxcast : (x : ℤ) = z % ((n/d : ℕ) : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hpos))
  have hbound : x < orderOf g := by
    rw [horder]
    exact_mod_cast (show (x : ℤ) < ((n/d : ℕ) : ℤ) by rw [hxcast]; exact Int.emod_lt_of_pos _ hpos)
  have hpower (hd : d ∣ v) : g ^ x = t := by
    have hmul : (d : ℤ) * ((v/d : ℕ) : ℤ) = (v : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hd
    have hmod : (u : ℤ) * z ≡ (v : ℤ) [ZMOD (orderOf h : ℤ)] := by
      rw [hh]
      change (u : ℤ) * (Nat.gcdA u n * _) ≡ (v : ℤ) [ZMOD (n : ℤ)]
      rw [← mul_assoc, ← hmul]
      exact (Int.gcd_a_modEq u n).mul_right _
    calc
      g ^ x = g ^ (z % (orderOf g : ℤ)) := by rw [← zpow_natCast, hxcast, horder]
      _ = g ^ z := zpow_mod_orderOf _ _
      _ = h ^ ((u : ℤ) * z) := by rw [zpow_mul h (u : ℤ) z, zpow_natCast, hgu]
      _ = h ^ (v : ℤ) := zpow_eq_zpow_iff_modEq.mpr hmod
      _ = t := by rw [zpow_natCast, htv]
  have hnecess (ht : t ∈ Subgroup.zpowers g) : d ∣ v := by
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ht)
    have hmod : u * k ≡ v [MOD n] := by
      change u * k ≡ v [MOD p - 1]
      rw [← hh, ← pow_eq_pow_iff_modEq (x := h), pow_mul, hgu, hk, htv]
    exact (hmod.dvd_iff (Nat.gcd_dvd_right u n)).mp
      ((Nat.gcd_dvd_left u n).trans (dvd_mul_right u k))
  constructor
  · intro ht
    have hd : ¬d ∣ v := fun hdiv => ht (hpower hdiv ▸ (Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) x)
    simpa only [if_neg hd] using hout
  · intro ht
    have hd := hnecess ht
    exact ⟨x, hbound, hpower hd, by simpa only [if_pos hd] using hout⟩
