-- Prove2me | solution 1 for ECDLP.p_prime
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:27:59.694602+00:00
-- url     : https://prove2.me/submissions/4f81f00c-5acf-4454-9792-f12c44856988

import Mathlib
import Definitions.Def_ECDLPChallengeData

lemma lucas_cert (p : ℕ) (a : ZMod p) (PL : List (ℕ × ℕ))
    (hprime : ∀ x ∈ PL, x.1.Prime) (hprod : p - 1 = (PL.map fun x => x.1 ^ x.2).prod)
    (ha : a ^ (p - 1) = 1) (hd : ∀ x ∈ PL, a ^ ((p - 1) / x.1) ≠ 1) : p.Prime := by
  apply lucas_primality p a ha
  intro q hq hqd
  rw [hprod] at hqd
  obtain ⟨y, hy, hqy⟩ := (Prime.dvd_prod_iff hq.prime).mp hqd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  have hqx : q ∣ x.1 := hq.dvd_of_dvd_pow hqy
  have heq : q = x.1 := (Nat.prime_dvd_prime_iff_eq hq (hprime x hx)).mp hqx
  rw [heq]
  exact hd x hx
theorem prime_160217 : Nat.Prime 160217 :=
  lucas_cert 160217 (3 : ZMod 160217) [(2, 3), (7, 1), (2861, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_10365719467 : Nat.Prime 10365719467 :=
  lucas_cert 10365719467 (2 : ZMod 10365719467) [(2, 1), (3, 1), (41, 1), (263, 1), (160217, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_160217, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_16647345464003 : Nat.Prime 16647345464003 :=
  lucas_cert 16647345464003 (5 : ZMod 16647345464003) [(2, 1), (11, 1), (73, 1), (10365719467, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, prime_10365719467, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_14102437 : Nat.Prime 14102437 :=
  lucas_cert 14102437 (2 : ZMod 14102437) [(2, 2), (3, 1), (439, 1), (2677, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_284059 : Nat.Prime 284059 :=
  lucas_cert 284059 (2 : ZMod 284059) [(2, 1), (3, 2), (43, 1), (367, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_1136237 : Nat.Prime 1136237 :=
  lucas_cert 1136237 (2 : ZMod 1136237) [(2, 2), (284059, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, prime_284059, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_10505209417 : Nat.Prime 10505209417 :=
  lucas_cert 10505209417 (5 : ZMod 10505209417) [(2, 3), (3, 1), (13, 1), (71, 1), (97, 1), (4889, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_1131135619504004412981251 : Nat.Prime 1131135619504004412981251 :=
  lucas_cert 1131135619504004412981251 (6 : ZMod 1131135619504004412981251) [(2, 1), (5, 5), (17, 1), (26357, 1), (38449, 1), (10505209417, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, prime_10505209417, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_60411691166469867688502653409 : Nat.Prime 60411691166469867688502653409 :=
  lucas_cert 60411691166469867688502653409 (3 : ZMod 60411691166469867688502653409) [(2, 5), (1669, 1), (1131135619504004412981251, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, prime_1131135619504004412981251, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_121496337762571714803422705240623021411 : Nat.Prime 121496337762571714803422705240623021411 :=
  lucas_cert 121496337762571714803422705240623021411 (3 : ZMod 121496337762571714803422705240623021411) [(2, 1), (3, 1), (5, 1), (59, 1), (1136237, 1), (60411691166469867688502653409, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_1136237, prime_60411691166469867688502653409, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_3430570593063974939189443505174231632560997 : Nat.Prime 3430570593063974939189443505174231632560997 :=
  lucas_cert 3430570593063974939189443505174231632560997 (2 : ZMod 3430570593063974939189443505174231632560997) [(2, 2), (3, 1), (13, 1), (181, 1), (121496337762571714803422705240623021411, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_121496337762571714803422705240623021411, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_308229906645612020336293120052894363722340458456001 : Nat.Prime 308229906645612020336293120052894363722340458456001 :=
  lucas_cert 308229906645612020336293120052894363722340458456001 (3 : ZMod 308229906645612020336293120052894363722340458456001) [(2, 6), (5, 3), (11, 1), (1021, 1), (3430570593063974939189443505174231632560997, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_3430570593063974939189443505174231632560997, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_15187694182909773202264112131543351735580574976896488582282879 : Nat.Prime 15187694182909773202264112131543351735580574976896488582282879 :=
  lucas_cert 15187694182909773202264112131543351735580574976896488582282879 (7 : ZMod 15187694182909773202264112131543351735580574976896488582282879) [(2, 1), (1747, 1), (14102437, 1), (308229906645612020336293120052894363722340458456001, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, prime_14102437, prime_308229906645612020336293120052894363722340458456001, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)

theorem prime_92031864238688105485400538143121826382268912998421731683072033206257804487869 : Nat.Prime 92031864238688105485400538143121826382268912998421731683072033206257804487869 :=
  lucas_cert 92031864238688105485400538143121826382268912998421731683072033206257804487869 (2 : ZMod 92031864238688105485400538143121826382268912998421731683072033206257804487869) [(2, 2), (7, 1), (13, 1), (16647345464003, 1), (15187694182909773202264112131543351735580574976896488582282879, 1)]
    (by simp only [List.forall_mem_cons]; exact ⟨by norm_num, by norm_num, by norm_num, prime_16647345464003, prime_15187694182909773202264112131543351735580574976896488582282879, by simp⟩)
    (by norm_num)
    (by reduce_mod_char)
    (by simp only [List.forall_mem_cons]; exact ⟨by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by reduce_mod_char; decide, by simp⟩)


theorem solution : Nat.Prime ECDLP.p := prime_92031864238688105485400538143121826382268912998421731683072033206257804487869
