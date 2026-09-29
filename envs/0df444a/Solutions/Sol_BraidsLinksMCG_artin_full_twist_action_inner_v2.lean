-- Prove2me | solution 1 for BraidsLinksMCG.artin_full_twist_action_inner_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T15:23:51.408801+00:00
-- url     : https://prove2.me/submissions/05525505-8c26-47c0-a9ec-0e324845e90e

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_prefix_product_action_inner_v1

open BraidsLinksMCG

theorem solution
    (n : ℕ)
    (hn : 2 ≤ n)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      xi (sigma i) w = artinEndo n i w) :
    ∀ w : FreeGroup (Fin n),
      xi (sigmaProd n ^ n) w =
        freeWordProd n * w * (freeWordProd n)⁻¹ := by
  let z : Fin n := ⟨0, by omega⟩
  let L : List (MulAut (FreeGroup (Fin n))) :=
    List.ofFn (fun i : Fin (n - 1) => xi (sigma i))
  let X : List (FreeGroup (Fin n)) :=
    List.ofFn (fun j : Fin n => FreeGroup.of j)
  let pref (k : ℕ) : FreeGroup (Fin n) := (X.take k).prod
  let shift (k : ℕ) (j : Fin n) : Fin n :=
    ⟨(j.val + k) % n, Nat.mod_lt _ (by omega)⟩
  let expected (k : ℕ) (hk : k < n) (j : Fin n) : FreeGroup (Fin n) :=
    if h : j.val < k then
      FreeGroup.of z * FreeGroup.of ⟨j.val + 1, by omega⟩ *
        (FreeGroup.of z)⁻¹
    else if h : j.val = k then
      FreeGroup.of z
    else
      FreeGroup.of j
  have hxi_prefix (k : ℕ) (hk : k ≤ n - 1) :
      xi ((List.ofFn (fun i : Fin (n - 1) => sigma i)).take k).prod =
        (L.take k).prod := by
    calc
      xi ((List.ofFn (fun i : Fin (n - 1) => sigma i)).take k).prod =
          (((List.ofFn (fun i : Fin (n - 1) => sigma i)).take k).map xi).prod :=
        (List.prod_hom _ xi).symm
      _ = (((List.ofFn (fun i : Fin (n - 1) => sigma i)).map xi).take k).prod := by
        rw [List.map_take]
      _ = (L.take k).prod := by
        simpa only [L, List.map_ofFn, Function.comp_def]
  have hxi_prod : xi (sigmaProd n) = L.prod := by
    calc
      xi (sigmaProd n) =
          xi ((List.ofFn (fun i : Fin (n - 1) => sigma i)).prod) := rfl
      _ = ((List.ofFn (fun i : Fin (n - 1) => sigma i)).map xi).prod :=
        (List.prod_hom _ xi).symm
      _ = (List.ofFn (fun i : Fin (n - 1) => xi (sigma i))).prod := by
        simpa only [L, List.map_ofFn, Function.comp_def]
  have hgen (j : Fin n) :
      xi (sigmaProd n) (FreeGroup.of j) =
        FreeGroup.of z * FreeGroup.of (shift 1 j) * (FreeGroup.of z)⁻¹ := by
    rw [hxi_prod]
    have hlen : L.length = n - 1 := by
      simp [L]
    have htake : L.take (n - 1) = L := by
      exact List.take_of_length_le hlen.le
    rw [← htake]
    rw [← hxi_prefix (n - 1) (by omega)]
    have h := artin_prefix_product_action_inner_v1 n hn xi hxi
      (n - 1) (by omega) j
    by_cases hj : j.val < n - 1
    · have hj' : j.val + 1 < n := by omega
      simpa [expected, hj, shift, Nat.mod_eq_of_lt hj'] using h
    · have hj' : j.val = n - 1 := by omega
      have hshift : shift 1 j = z := by
        apply Fin.ext
        change (j.val + 1) % n = 0
        rw [show j.val + 1 = n by omega, Nat.mod_self]
      simpa [expected, hj, hj', hshift] using h
  have hpref_succ (k : ℕ) (hk : k < n) :
      pref (k + 1) = pref k * FreeGroup.of (⟨k, hk⟩ : Fin n) := by
    dsimp [pref]
    rw [List.prod_take_succ X k (by simpa [X] using hk)]
    simp [X, hk]
  have hpow_gen : ∀ k : ℕ, k ≤ n → ∀ j : Fin n,
      (xi (sigmaProd n) ^ k) (FreeGroup.of j) =
        pref k * FreeGroup.of (shift k j) * (pref k)⁻¹ := by
    intro k
    induction k with
    | zero =>
        intro _ j
        have hshift0 : shift 0 j = j := by
          apply Fin.ext
          simp [shift, Nat.mod_eq_of_lt j.isLt]
        simp [pref, hshift0]
    | succ k ih =>
        intro hk j
        have hklt : k < n := by omega
        have hk' : k ≤ n := by omega
        have hs0 : shift k z = (⟨k, hklt⟩ : Fin n) := by
          apply Fin.ext
          simp [shift, z, Nat.mod_eq_of_lt hklt]
        have hss : shift k (shift 1 j) = shift (k + 1) j := by
          apply Fin.ext
          simp only [shift]
          rw [Nat.mod_add_mod]
          congr 1
          omega
        rw [pow_succ, MulAut.mul_apply, hgen]
        simp only [map_mul, map_inv]
        rw [ih hk' z, ih hk' (shift 1 j), hs0, hss,
          hpref_succ k hklt]
        group
  have hprefN : pref n = freeWordProd n := by
    dsimp [pref]
    rw [List.take_of_length_le (by simp [X])]
    simp [X, freeWordProd]
  have hshiftN (j : Fin n) : shift n j = j := by
    apply Fin.ext
    simp [shift, Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  have hpow_on_generators (j : Fin n) :
      (xi (sigmaProd n) ^ n) (FreeGroup.of j) =
        (MulAut.conj (freeWordProd n)) (FreeGroup.of j) := by
    simpa [hprefN, hshiftN, MulAut.conj_apply] using
      hpow_gen n (by omega) j
  have hmh :
      (xi (sigmaProd n) ^ n).toMonoidHom =
        (MulAut.conj (freeWordProd n)).toMonoidHom := by
    apply FreeGroup.ext_hom
    exact hpow_on_generators
  have hfull : xi (sigmaProd n) ^ n = MulAut.conj (freeWordProd n) := by
    apply MulEquiv.ext
    intro w
    exact congrArg (fun h : FreeGroup (Fin n) →* FreeGroup (Fin n) => h w) hmh
  intro w
  rw [map_pow, hfull]
  exact MulAut.conj_apply _ _
