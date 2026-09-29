-- Prove2me | solution 1 for BraidsLinksMCG.artin_prefix_product_action_inner_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T14:54:12.406663+00:00
-- url     : https://prove2.me/submissions/dfbe3285-928f-46b6-80f1-0b1e6e70f93c

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

open BraidsLinksMCG

theorem solution
    (n : ℕ)
    (hn : 2 ≤ n)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      xi (sigma i) w = artinEndo n i w)
    (k : ℕ)
    (hk : k ≤ n - 1)
    (j : Fin n) :
    xi ((List.ofFn (fun i : Fin (n - 1) => sigma i)).take k).prod
        (FreeGroup.of j) =
      if h : j.val < k then
        FreeGroup.of ⟨0, by omega⟩ *
          FreeGroup.of ⟨j.val + 1, by omega⟩ *
          (FreeGroup.of ⟨0, by omega⟩)⁻¹
      else if h : j.val = k then
        FreeGroup.of ⟨0, by omega⟩
      else
        FreeGroup.of j := by
  let z : Fin n := ⟨0, by omega⟩
  let L : List (MulAut (FreeGroup (Fin n))) :=
    List.ofFn (fun i : Fin (n - 1) => xi (sigma i))
  let expected (k : ℕ) (hk : k < n) (j : Fin n) : FreeGroup (Fin n) :=
    if h : j.val < k then
      FreeGroup.of z * FreeGroup.of ⟨j.val + 1, by omega⟩ *
        (FreeGroup.of z)⁻¹
    else if h : j.val = k then
      FreeGroup.of z
    else
      FreeGroup.of j
  have hA (i : Fin (n - 1)) (j : Fin n) :
      xi (sigma i) (FreeGroup.of j) =
        if j = strandIdx (n := n) i then
          FreeGroup.of (strandIdx (n := n) i) *
            FreeGroup.of (strandIdxSucc (n := n) i) *
            (FreeGroup.of (strandIdx (n := n) i))⁻¹
        else if j = strandIdxSucc (n := n) i then
          FreeGroup.of (strandIdx (n := n) i)
        else
          FreeGroup.of j := by
    simpa only [artinEndo, FreeGroup.lift_apply_of] using hxi i (FreeGroup.of j)
  have hprefix : ∀ (k : ℕ) (hk : k < n) (j : Fin n),
      (L.take k).prod (FreeGroup.of j) = expected k hk j := by
    intro k
    induction k with
    | zero =>
        intro hk j
        by_cases hj : j.val = 0
        · have hjz : j = z := by
            apply Fin.ext
            exact hj
          subst j
          simp [expected, z]
        · simp [expected, hj]
    | succ k ih =>
        intro hk j
        have hklt : k < n - 1 := by omega
        let ki : Fin (n - 1) := ⟨k, hklt⟩
        let kj0 : Fin n := ⟨k, by omega⟩
        let kj1 : Fin n := ⟨k + 1, by omega⟩
        have hki : strandIdx (n := n) ki = kj0 := by
          apply Fin.ext
          rfl
        have hki1 : strandIdxSucc (n := n) ki = kj1 := by
          apply Fin.ext
          rfl
        have hkj0 : (kj0 : Fin n).val = k := rfl
        have hkj1 : (kj1 : Fin n).val = k + 1 := rfl
        have hlen : k < L.length := by
          simpa [L] using hklt
        have hLk : L[k] = xi (sigma ki) := by
          change (List.ofFn (fun i : Fin (n - 1) => xi (sigma i)))[k] =
            xi (sigma ki)
          have hklen : k < (List.ofFn (fun i : Fin (n - 1) => xi (sigma i))).length := by
            simpa [L] using hklt
          rw [List.getElem_ofFn hklen]
        have hA_cases (v : Fin n) :
            xi (sigma ki) (FreeGroup.of v) =
              if v = kj0 then
                FreeGroup.of kj0 * FreeGroup.of kj1 *
                  (FreeGroup.of kj0)⁻¹
              else if v = kj1 then
                FreeGroup.of kj0
              else
                FreeGroup.of v := by
          rw [hA ki v, hki, hki1]
        have hA_num (v : Fin n) :
            xi (sigma ki) (FreeGroup.of v) =
              if v.val < k then
                FreeGroup.of v
              else if v.val = k then
                FreeGroup.of kj0 * FreeGroup.of kj1 *
                  (FreeGroup.of kj0)⁻¹
              else if v.val = k + 1 then
                FreeGroup.of kj0
              else
                FreeGroup.of v := by
          by_cases hvlt : v.val < k
          · have hv0' : v ≠ kj0 := by
              intro heq
              have hval := congrArg Fin.val heq
              simp [kj0] at hval
              omega
            have hv1' : v ≠ kj1 := by
              intro heq
              have hval := congrArg Fin.val heq
              simp [kj1] at hval
              omega
            rw [hA_cases]
            simp [hvlt, hv0', hv1', show v.val ≠ k by omega,
              show v.val ≠ k + 1 by omega]
          · by_cases hv0 : v.val = k
            · have hv0' : v = kj0 := by
                apply Fin.ext
                exact hv0
              subst v
              rw [hA_cases]
              have hkj0ne : kj0 ≠ kj1 := by
                intro heq
                have hval := congrArg Fin.val heq
                simp [kj0, kj1] at hval
              simp [kj0, kj1, hkj0ne]
            · by_cases hv1 : v.val = k + 1
              · have hv1' : v = kj1 := by
                  apply Fin.ext
                  exact hv1
                subst v
                rw [hA_cases]
                have hkj1ne : kj1 ≠ kj0 := by
                  intro heq
                  have hval := congrArg Fin.val heq
                  simp [kj0, kj1] at hval
                simp [kj0, kj1, hkj1ne]
              · have hv0' : v ≠ kj0 := by
                  intro heq
                  have hval := congrArg Fin.val heq
                  simp [kj0] at hval
                  omega
                have hv1' : v ≠ kj1 := by
                  intro heq
                  have hval := congrArg Fin.val heq
                  simp [kj1] at hval
                  omega
                rw [hA_cases]
                simp [hvlt, hv0, hv1, hv0', hv1']
        rw [List.prod_take_succ L k hlen, hLk, MulAut.mul_apply]
        by_cases h1 : j.val < k
        · have hAj : xi (sigma ki) (FreeGroup.of j) = FreeGroup.of j := by
            rw [hA_num j]
            simp [h1, show j.val ≠ k by omega, show j.val ≠ k + 1 by omega]
          have ih' :
              (List.take k L).prod (FreeGroup.of j) =
                FreeGroup.of z *
                  FreeGroup.of ⟨j.val + 1, by omega⟩ *
                  (FreeGroup.of z)⁻¹ := by
            simpa [expected, h1, show j.val ≠ k by omega,
              show j.val ≠ k + 1 by omega] using ih (by omega) j
          calc
            (List.take k L).prod (xi (sigma ki) (FreeGroup.of j)) =
                (List.take k L).prod (FreeGroup.of j) := by rw [hAj]
            _ = FreeGroup.of z *
                FreeGroup.of ⟨j.val + 1, by omega⟩ *
                (FreeGroup.of z)⁻¹ := ih'
            _ = expected (k + 1) hk j := by
              have hjlt : j.val < k + 1 := by omega
              have hjne : j.val ≠ k + 1 := by omega
              simp [expected, hjlt, hjne, show j.val ≠ k by omega]
        · by_cases h2 : j.val = k
          · have hAj : xi (sigma ki) (FreeGroup.of j) =
                FreeGroup.of kj0 * FreeGroup.of kj1 *
                  (FreeGroup.of kj0)⁻¹ := by
              rw [hA_num j]
              simp [h2, h1]
            have hp0 := ih (by omega) kj0
            have hp1 := ih (by omega) kj1
            have hp0' :
                (List.take k L).prod (FreeGroup.of kj0) =
                  FreeGroup.of z := by
              simpa [expected, hkj0, hk] using hp0
            have hp1' :
                (List.take k L).prod (FreeGroup.of kj1) =
                  FreeGroup.of kj1 := by
              simpa [expected, hkj1, hk] using hp1
            have hp0inv :
                (List.take k L).prod (FreeGroup.of kj0)⁻¹ =
                  (FreeGroup.of z)⁻¹ := by
              simpa only [map_inv] using congrArg Inv.inv hp0'
            calc
              (List.take k L).prod (xi (sigma ki) (FreeGroup.of j)) =
                  (List.take k L).prod
                    (FreeGroup.of kj0 * FreeGroup.of kj1 *
                      (FreeGroup.of kj0)⁻¹) := by rw [hAj]
              _ = (List.take k L).prod (FreeGroup.of kj0) *
                  (List.take k L).prod (FreeGroup.of kj1) *
                  (List.take k L).prod (FreeGroup.of kj0)⁻¹ := by
                    simp only [map_mul, map_inv]
              _ = FreeGroup.of z * FreeGroup.of kj1 *
                  (FreeGroup.of z)⁻¹ := by
                    rw [hp0', hp1', hp0inv]
              _ = expected (k + 1) hk j := by
                have hjlt : j.val < k + 1 := by omega
                have hjne : j.val ≠ k + 1 := by omega
                have hjsucc : kj1 = (⟨j.val + 1, by omega⟩ : Fin n) := by
                  apply Fin.ext
                  change k + 1 = j.val + 1
                  omega
                rw [hjsucc]
                simp [expected, hjlt, hjne]
          · by_cases h3 : j.val = k + 1
            · have hAj : xi (sigma ki) (FreeGroup.of j) = FreeGroup.of kj0 := by
                rw [hA_num j]
                simp [h1, h2, h3]
              have hp0 := ih (by omega) kj0
              have hp0' :
                  (List.take k L).prod (FreeGroup.of kj0) =
                    FreeGroup.of z := by
                simpa [expected, hkj0, hk] using hp0
              calc
                (List.take k L).prod (xi (sigma ki) (FreeGroup.of j)) =
                    (List.take k L).prod (FreeGroup.of kj0) := by rw [hAj]
                _ = FreeGroup.of z := hp0'
                _ = expected (k + 1) hk j := by
                  have hjge : ¬ j.val < k + 1 :=
                    Nat.not_lt_of_ge (Nat.le_of_eq h3.symm)
                  simp [expected, hjge, h3]
            · have hAj : xi (sigma ki) (FreeGroup.of j) = FreeGroup.of j := by
                rw [hA_num j]
                simp [h1, h2, h3]
              calc
                (List.take k L).prod (xi (sigma ki) (FreeGroup.of j)) =
                    (List.take k L).prod (FreeGroup.of j) := by rw [hAj]
                _ = expected (k + 1) hk j := by
                  have hjge : ¬ j.val < k + 1 := by
                    intro hlt
                    have hjle : j.val ≤ k := Nat.le_of_lt_succ hlt
                    have hjeq : j.val = k :=
                      Nat.le_antisymm hjle (Nat.not_lt.mp h1)
                    exact h2 hjeq
                  simpa [expected, h1, h2, h3, hjge] using
                    ih (by omega) j
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
  rw [hxi_prefix k hk]
  simpa [expected, z] using hprefix k (by omega) j
