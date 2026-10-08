-- Prove2me | solution 1 for ErdosStraus242.hard_core_840_after_79_sieves
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T11:23:06.138041+00:00
-- url     : https://prove2.me/submissions/e3ba79b8-3441-49d4-9d3a-39154e90e60a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Theorems.Thm_ErdosStraus242_family_mod703
import Theorems.Thm_ErdosStraus242_family_mod719
import Theorems.Thm_ErdosStraus242_family_mod727
import Theorems.Thm_ErdosStraus242_family_mod731
import Theorems.Thm_ErdosStraus242_family_mod739
import Theorems.Thm_ErdosStraus242_family_mod743
import Theorems.Thm_ErdosStraus242_family_mod751
import Theorems.Thm_ErdosStraus242_family_mod767
import Theorems.Thm_ErdosStraus242_family_mod779
import Theorems.Thm_ErdosStraus242_family_mod787
import Theorems.Thm_ErdosStraus242_family_mod799
import Theorems.Thm_ErdosStraus242_family_mod803
import Theorems.Thm_ErdosStraus242_family_mod811
import Theorems.Thm_ErdosStraus242_family_mod823
import Theorems.Thm_ErdosStraus242_family_mod827
import Theorems.Thm_ErdosStraus242_family_mod839
import Theorems.Thm_ErdosStraus242_hard_core_840_after_95_sieves

open ErdosStraus242

theorem solution (p : ℕ) (hp : Nat.Prime p) (hp2 : 2 < p)
    (hres : p % 840 ∈ ({1, 121, 169, 289, 361, 529} : Finset ℕ))
    (h11 : p % 11 ∉ ({7, 8, 10} : Finset ℕ))
    (h19 : p % 19 ∉ ({14, 15, 18} : Finset ℕ))
    (h23 : p % 23 ∉ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ))
    (h31 : p % 31 ∉ ({23, 27} : Finset ℕ))
    (h43 : p % 43 ∉ ({39} : Finset ℕ))
    (h47 : p % 47 ∉ ({35} : Finset ℕ))
    (h59 : p % 59 ∉ ({47} : Finset ℕ))
    (h67 : p % 67 ∉ ({63} : Finset ℕ))
    (h71 : p % 71 ∉ ({59} : Finset ℕ))
    (h79 : p % 79 ∉ ({39, 59, 63, 71, 75} : Finset ℕ))
    (h83 : p % 83 ∉ ({55} : Finset ℕ))
    (h103 : p % 103 ∉ ({99, 95, 51} : Finset ℕ))
    (h107 : p % 107 ∉ ({71} : Finset ℕ))
    (h127 : p % 127 ∉ ({123, 119, 111, 95, 63} : Finset ℕ))
    (h131 : p % 131 ∉ ({119} : Finset ℕ))
    (h139 : p % 139 ∉ ({111} : Finset ℕ))
    (h143 : p % 143 ∉ ({71, 95, 107, 119, 127, 131, 135, 139} : Finset ℕ))
    (h151 : p % 151 ∉ ({143} : Finset ℕ))
    (h163 : p % 163 ∉ ({159} : Finset ℕ))
    (h167 : p % 167 ∉ ({163} : Finset ℕ))
    (h179 : p % 179 ∉ ({119} : Finset ℕ))
    (h187 : p % 187 ∉ ({183} : Finset ℕ))
    (h191 : p % 191 ∉ ({127} : Finset ℕ))
    (h199 : p % 199 ∉ ({179} : Finset ℕ))
    (h211 : p % 211 ∉ ({207} : Finset ℕ))
    (h223 : p % 223 ∉ ({215} : Finset ℕ))
    (h227 : p % 227 ∉ ({151} : Finset ℕ))
    (h239 : p % 239 ∉ ({231} : Finset ℕ))
    (h247 : p % 247 ∉ ({243, 239, 123} : Finset ℕ))
    (h251 : p % 251 ∉ ({167} : Finset ℕ))
    (h263 : p % 263 ∉ ({255} : Finset ℕ))
    (h271 : p % 271 ∉ ({267} : Finset ℕ))
    (h283 : p % 283 ∉ ({279} : Finset ℕ))
    (h299 : p % 299 ∉ ({295, 287, 279, 239, 199} : Finset ℕ))
    (h307 : p % 307 ∉ ({263} : Finset ℕ))
    (h311 : p % 311 ∉ ({259} : Finset ℕ))
    (h319 : p % 319 ∉ ({315, 311, 303, 299, 287, 279, 255, 239, 159} : Finset ℕ))
    (h323 : p % 323 ∉ ({319, 311, 287, 215} : Finset ℕ))
    (h331 : p % 331 ∉ ({327} : Finset ℕ))
    (h347 : p % 347 ∉ ({335} : Finset ℕ))
    (h359 : p % 359 ∉ ({323} : Finset ℕ))
    (h367 : p % 367 ∉ ({363} : Finset ℕ))
    (h379 : p % 379 ∉ ({303} : Finset ℕ))
    (h383 : p % 383 ∉ ({311} : Finset ℕ))
    (h391 : p % 391 ∉ ({387, 383, 363, 335, 195} : Finset ℕ))
    (h403 : p % 403 ∉ ({399} : Finset ℕ))
    (h407 : p % 407 ∉ ({403, 399, 395, 383, 339, 271, 203} : Finset ℕ))
    (h419 : p % 419 ∉ ({391} : Finset ℕ))
    (h431 : p % 431 ∉ ({407} : Finset ℕ))
    (h439 : p % 439 ∉ ({419} : Finset ℕ))
    (h443 : p % 443 ∉ ({431} : Finset ℕ))
    (h451 : p % 451 ∉ ({447} : Finset ℕ))
    (h463 : p % 463 ∉ ({459, 455, 447, 347, 231} : Finset ℕ))
    (h467 : p % 467 ∉ ({463} : Finset ℕ))
    (h487 : p % 487 ∉ ({483, 479, 243} : Finset ℕ))
    (h491 : p % 491 ∉ ({487, 479, 327} : Finset ℕ))
    (h499 : p % 499 ∉ ({495, 479, 399} : Finset ℕ))
    (h503 : p % 503 ∉ ({499, 495, 491, 479, 475, 467, 447, 431, 419, 335, 251} : Finset ℕ))
    (h523 : p % 523 ∉ ({519} : Finset ℕ))
    (h527 : p % 527 ∉ ({523, 519, 515, 511, 503, 483, 479, 439, 395, 351, 263} : Finset ℕ))
    (h547 : p % 547 ∉ ({543} : Finset ℕ))
    (h551 : p % 551 ∉ ({547, 543, 539, 527, 459, 367, 275} : Finset ℕ))
    (h559 : p % 559 ∉ ({555, 551, 543, 539, 531, 519, 503, 479, 447, 419, 279} : Finset ℕ))
    (h563 : p % 563 ∉ ({559, 551, 375} : Finset ℕ))
    (h571 : p % 571 ∉ ({567, 527, 519} : Finset ℕ))
    (h583 : p % 583 ∉ ({579, 575, 291} : Finset ℕ))
    (h587 : p % 587 ∉ ({583, 575, 559, 503, 391} : Finset ℕ))
    (h599 : p % 599 ∉ ({595, 591, 587, 579, 575, 559, 539, 499, 479, 399, 299} : Finset ℕ))
    (h607 : p % 607 ∉ ({603, 599, 591, 575, 531, 455, 303} : Finset ℕ))
    (h611 : p % 611 ∉ ({607, 599, 575, 543, 407} : Finset ℕ))
    (h619 : p % 619 ∉ ({615, 599, 495} : Finset ℕ))
    (h631 : p % 631 ∉ ({627, 623, 315} : Finset ℕ))
    (h643 : p % 643 ∉ ({639, 615, 551} : Finset ℕ))
    (h647 : p % 647 ∉ ({643, 639, 635, 623, 611, 575, 539, 431, 323} : Finset ℕ))
    (h659 : p % 659 ∉ ({655, 647, 639, 615, 599, 527, 439} : Finset ℕ))
    (h667 : p % 667 ∉ ({663} : Finset ℕ))
    (h671 : p % 671 ∉ ({667, 663, 659, 655, 647, 643, 639, 623, 615, 587, 575, 559, 503, 447, 335} : Finset ℕ))
    (h683 : p % 683 ∉ ({679, 671, 647, 607, 455} : Finset ℕ))
    (h691 : p % 691 ∉ ({687} : Finset ℕ))
    : IsErdosStraus p := by
  by_cases h703 : p % 703 ∈ ({699, 695, 687, 671, 659, 639, 615, 527, 351} : Finset ℕ)
  · exact family_mod703 p hp2 h703
  ·
    by_cases h719 : p % 719 ∈ ({715, 711, 707, 703, 699, 695, 683, 679, 671, 659, 647, 639, 599, 575, 539, 479, 359} : Finset ℕ)
    · exact family_mod719 p hp2 h719
    ·
      by_cases h727 : p % 727 ∈ ({723, 719, 699, 675, 671, 623, 363} : Finset ℕ)
      · exact family_mod727 p hp2 h727
      ·
        by_cases h731 : p % 731 ∈ ({727, 719, 487} : Finset ℕ)
        · exact family_mod731 p hp2 h731
        ·
          by_cases h739 : p % 739 ∈ ({735, 719, 591} : Finset ℕ)
          · exact family_mod739 p hp2 h739
          ·
            by_cases h743 : p % 743 ∈ ({739, 735, 731, 719, 619, 495, 371} : Finset ℕ)
            · exact family_mod743 p hp2 h743
            ·
              by_cases h751 : p % 751 ∈ ({747, 743, 735, 563, 375} : Finset ℕ)
              · exact family_mod751 p hp2 h751
              ·
                by_cases h767 : p % 767 ∈ ({763, 759, 755, 751, 743, 735, 719, 703, 671, 639, 575, 511, 383} : Finset ℕ)
                · exact family_mod767 p hp2 h767
                ·
                  by_cases h779 : p % 779 ∈ ({775, 767, 759, 727, 719, 623, 519} : Finset ℕ)
                  · exact family_mod779 p hp2 h779
                  ·
                    by_cases h787 : p % 787 ∈ ({783} : Finset ℕ)
                    · exact family_mod787 p hp2 h787
                    ·
                      by_cases h799 : p % 799 ∈ ({795, 791, 783, 779, 767, 759, 719, 699, 639, 599, 399} : Finset ℕ)
                      · exact family_mod799 p hp2 h799
                      ·
                        by_cases h803 : p % 803 ∈ ({799, 791, 535} : Finset ℕ)
                        · exact family_mod803 p hp2 h803
                        ·
                          by_cases h811 : p % 811 ∈ ({807, 783, 695} : Finset ℕ)
                          · exact family_mod811 p hp2 h811
                          ·
                            by_cases h823 : p % 823 ∈ ({819, 815, 411} : Finset ℕ)
                            · exact family_mod823 p hp2 h823
                            ·
                              by_cases h827 : p % 827 ∈ ({823, 815, 791, 735, 551} : Finset ℕ)
                              · exact family_mod827 p hp2 h827
                              ·
                                by_cases h839 : p % 839 ∈ ({835, 831, 827, 819, 815, 811, 799, 783, 779, 755, 719, 699, 671, 559, 419} : Finset ℕ)
                                · exact family_mod839 p hp2 h839
                                ·
                                  exact hard_core_840_after_95_sieves p hp hp2 hres h11 h19 h23 h31 h43 h47 h59 h67 h71 h79 h83 h103 h107 h127 h131 h139 h143 h151 h163 h167 h179 h187 h191 h199 h211 h223 h227 h239 h247 h251 h263 h271 h283 h299 h307 h311 h319 h323 h331 h347 h359 h367 h379 h383 h391 h403 h407 h419 h431 h439 h443 h451 h463 h467 h487 h491 h499 h503 h523 h527 h547 h551 h559 h563 h571 h583 h587 h599 h607 h611 h619 h631 h643 h647 h659 h667 h671 h683 h691 h703 h719 h727 h731 h739 h743 h751 h767 h779 h787 h799 h803 h811 h823 h827 h839
